{-# LANGUAGE LambdaCase, StandaloneDeriving, DeriveDataTypeable #-}
module Desugar.Desugar where
--A separate module for desugaring; Compiler should just tie each stage
--together and handle the IO.

import Util (complainIf,(?),(!))
--import E.Par (pM,myLexer)
--import E.ErrM (Err(..))
import E.Abs (Ident(..),UIdent(..))
import qualified E.Abs as P

--CST -> AST
import AST.DTs
import AST.Util (rollTyApps)
import Desugar.DTs
import Desugar.T (desugarT)
import Desugar.Datatypes (processDTs)
import Desugar.SEP (desugarS,desugarE,desugarP)
--AST -> AST

import Data.Map (Map(..))
import qualified Data.Map as M hiding ((!))
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad (foldM,forM)
import Control.Monad.Trans.Except
import Control.Monad.State
import Text.Read (readMaybe)
import Data.List (sort)
import Data.Char (ord) --for string desugaring
import Control.Arrow ((***))
import Data.Maybe (fromMaybe)

import Data.Generics (Data(..),everything,mkQ,everywhere,mkT)

--Grouping declarations by constructor first leads to cleaner code, as I can
--get an overview of the handling for each decl type in one place.
--General principle: doing a task all at once in its own traversal is
--clearer and less bug-prone than the alternative (interspersing it with other
--code and maintaining invariants that ensures doing so is valid).
--It also lets me do more in Desugar since I can process decl types separately;
--in particular, it lets me desugar g => *g because I gather all globals first.
--I can also use minimal monad capabilities, reducing the risk of bugs.
--What do I need to do? Allocate new names in let bindings and new globals
--for strings; throw errors.
--That just requires StateT Int (Except err), where err can now be specific
--to each step.

--Groups elements of a showable datatype by top-level constructor.
--Precondition: it has no infix constructors...
--It's hacky and inefficient but simple.
--Unintended consequence: duplicate identical declarations are ignored.
--That's fine?
--Note it's no problem the order of decls is reversed since they should be
--order-independent anyway.
groupByCon :: Show a => [a] -> Map String [a]
groupByCon as =
  let kas = [(head $ words $ show a, a) | a <- as]
      empty = M.fromSet (const []) $ S.fromList $ words
        "Default Defun Instance TySig KindSig TySyn Import Global Data Tag"
  in foldr (\(k,a) m -> M.adjust (a:) k m) empty kas

--New desugar algo:
--First group decls by constructor
--Group each type of decl by its key; error on internal duplicates
-- defuns and instances are grouped together and are mutex
--Error on external duplicates:
--Dyn lowercase names: funs, vars
--Dyn uppercase: constructors
--Static (uppercase only): datatypes, tysyns, kinds
desugar :: P.M -> Either DError Module
desugar (P.Module ds) = do
  let nm2d = groupByCon ds
  --Four types need be desugared: STEP (S, T, E, Pat)
  --T can be desugared independently, but E desugaring relies on context
  --(and consequently S and Pat which contain Es do as well).
  --The context required is:
  --1) the global set (used for g=>*g in P,E)
  --2) boxed field status (used for bdt.field => *(...).fieldStructCon in E)
  --3) a string numbering m (used for "str" => *($string++show m["str"]))

  --globals
  gs <- groupGlobals nm2d
  --data
  dts <- groupEx "Data" (\(P.Data ca rhs) ->
                           let (nm,args) = desugarConArgs ca
                           in (nm,(args,rhs))) nm2d
  tags <- groupEx "Tag" (\(P.Tag ca pt contags) ->
                           let (nm,args) = desugarConArgs ca
                               t = desugarT pt
                               con2e = M.fromList $
                                 map (\(P.ConTag (UIdent con) pe) ->
                                        (con,pe)) contags
                           in (nm,(args,t,con2e)))  nm2d
  --kindsig
  --TyCon : Kind must be sorted out and moved to sorts
  ksigs <- groupEx "KindSig" (\(P.KindSig (UIdent nm) t) -> (nm, desugarT t))
    nm2d
  let ksigsForPDTs = M.filter (/=TyCon "Kind") ksigs
  let ks = M.keysSet $ M.filter (==TyCon "Kind") ksigs
  (dtsFull,ksigsFinal) <- processDTs dts tags ksigsForPDTs --Now we have 1)
  let gset = M.keysSet gs --Now we have 2)
  --To get the string numbering we need to collect the set of all string
  --literals in the source. That can be done cleanly by running an everything
  --on nm2d (which contains every decl).
  let strings :: Set String
      strings = everything S.union (mkQ S.empty $ \case
                                       P.String str -> S.singleton str
                                       _ -> S.empty) nm2d
      string2n = M.fromList $ zip (S.toList strings) [1..]
      --Now we have 3) and can define the DInfo
      --bdt.tagBDT is always unit; tag fields are never boxed.
      field2bcon = M.map (\(IsNormal _ bcon) -> bcon) $
                   M.filter (\case IsNormal b _ -> b
                                   _ -> False) $
                   fieldInfo dtsFull
      di = (gset,field2bcon,string2n)
  dtsFinal <- sepDTs di dtsFull
  --Also add string globals to global map
  gsFinal <- M.union (stringGlobals string2n) <$> sepGlobals di gs
  --default
  dflts <- groupEx "Default" (\(P.Default (UIdent nm) t) -> (nm, desugarT t))
    nm2d
  --tysig
  --tysigs also need string global tysigs inserted to fix their type
  tsigs <- M.union (stringTySigs string2n) <$>
    groupEx "TySig" (\(P.TySig (Ident nm) t) -> (nm, desugarT t)) nm2d
  
  --tysyn
  tsyns <- groupEx "TySyn" (\(P.TySyn ca t) ->
                              let (nm,args) = desugarConArgs ca
                              in (nm,(args, desugarT t))) nm2d
  --defun
  ds <- groupDefuns di nm2d
  --instance
  is <- groupInstances di $ nm2d ! "Instance"
  dis <- combineDefsAndInstances ds is
  --The module to return... but only if the checks pass
  let modul = Module {dtsInfo = dtsFinal,
                      globals = gsFinal,
                      defaults = dflts,
                      tysigs = tsigs,
                      kindsigs = ksigsFinal,
                      kinds = ks,
                      tysyns = tsyns,
                      defuns = dis
                     }
  --Validity checks:
  --No name clashes:
  --lowercase names: globals, functions
  do let fset = M.keysSet dis
     requireNoClash "Functions" "Globals" fset gset
     --Constructors have already been checked in Desugar.Datatypes
     --TyCons: datatypes, tysyns, kinds can clash
     let dts = M.keysSet $ datatypes dtsFinal
         syns = M.keysSet tsyns
     requireNoClash "DTs" "Tysyns" dts syns
     requireNoClash "DTs and Tysyns" "Kinds" (S.union dts syns) ks
     --All classes must have a signature
     let classFs = M.keysSet is
         sigs = M.keysSet tsigs
         lacking = S.difference classFs sigs
     complainIf (not $ S.null lacking)
       $ ClassFunctionsLackSignatures lacking
     --All type signatures must correspond to a fun or global
     let nakedSigs = S.difference sigs (S.union fset gset)
     complainIf (not $ S.null nakedSigs)
       $ TypeSignaturesLackBindings nakedSigs

  --Finally return
  return modul

requireNoClash :: String -> String -> Set Name -> Set Name ->
  Either DError ()
requireNoClash t1 t2 s1 s2 = do
  let conflict = S.intersection s1 s2
  complainIf (not $ S.null conflict)
    $ Clash t1 t2 conflict

--Creates the global info map given the string=>id map
--string2n["abc"] = n => gs[$string<n>] = (Code, Just (Array 97 98 99))
stringGlobals :: Map String Int -> Map Name (Region, Maybe E)
stringGlobals string2n =
  M.fromList $
  map (\(str,n) -> ("$string" ++ show n,
                     (Co, Just $ EArray Nothing $
                       map (EInteger . fromIntegral . ord) str))) $
  M.toList string2n
--Strings are also of a fixed type: Array len Byte
--TODO fuse the functions if it matters to perf...
stringTySigs :: Map String Int -> Map Name T
stringTySigs string2n =
  M.fromList $
  map (\(str,n) -> ("$string" ++ show n,
                    Array (TyNat $ fromIntegral $ length str) (UInt 1))) $
  M.toList string2n

--sep as in S,E,Pat, not separation
--Only conInfo needs to change since that's where the tags are
sepDTs :: DInfo -> DTsInfo P.E -> Either DError (DTsInfo E)
sepDTs di dti = do
  dts' <- mapM sepDT $ datatypes dti
  return dti{datatypes = dts'}
    where sepDT dtinfo = do
            ts' <- sepTagScheme $ dtTagScheme dtinfo
            return dtinfo{dtTagScheme = ts'}
          sepTagScheme = \case
            Nil -> return Nil
            N1 n -> return $ N1 n
            N16 -> return N16
            Custom t con2pe ->
              Custom t <$> mapM (desugarE di) con2pe
            
--Cons no longer contain tag info, so sepConInfo is id
{-    
  where sepConInfo (con, UBCon p tagPE cfs cr) = do
          tagE <- desugarE di tagPE
          return (con, UBCon p tagE cfs cr)
        sepConInfo (con,BCon a b c) = return (con, BCon a b c)
-}
--Global rules per region:
--Memory: may have initializer
--Storage, TStorage: must not
--Code: must
--Other regions: may not have globals
--We enforce that here.
sepGlobals :: DInfo -> Map Name (Region, Maybe P.E) ->
  Either DError (Map Name (Region, Maybe E))
sepGlobals di nm2rmpe = do
  let nm_rmpe = M.toList nm2rmpe
  nmre <- mapM (\(nm,(r,mpe)) -> do
                   complainIf (r `elem` [Ca,Re])
                     $ BadGlobalRegion nm r
                   e <- case mpe of
                          Just pe -> do
                            complainIf (r `elem` [St,TS])
                              $ MustNotHaveInitializer nm r
                            Just <$> desugarE di pe
                          Nothing -> do
                            complainIf (r == Co)
                              $ CodeGlobalMustHaveInitializer nm
                            return Nothing
                   return (nm,(r,e))) nm_rmpe
  return $ M.fromList nmre

--Converts strings to array literals
--Desugarings:
--g => *g (stateless, can be done on either E or P.E)
--"abc" => &newg where code newg = array(97,98,99)
-- Content-based string var naming would make the pretty output unreadable...
-- instead number them.
-- 1. Collect the set of strings, then number them.
-- 2. Create the string global set
-- 3. Substitute the strings for their corresponding globals (not &g).
--It's simpler to do on E.
--Don't apply & to the string global... that way ! can be applied to str
--directly, and it can be efficiently copied using *ptr = "foo".
--Ah... then I don't need a global, I can convert to array(1,2,3) directly.
--Arrays which ultimately never touch the stack should just be *copied.

--p += k, p++ => let-bind exprs in p, reuse same location
--Issue: I also want to convert P.E to E, and that may fail
--It's awkward to operate on the CST, but the AST E should not have the
--features being desugared away - that's the whole point!
--That means I must choose between operating on the CST, adding undesired
--constructs to E or merging all desugaring steps into a single CST -> AST jump.
--Long-term solution: first convert to an intermediate AST?
--Con form standardization: Con {field: p} for patterns, fully applied Con
--for exprs.
--bdt.field => *(...).field' in exprs
--Pattern decomposition is deferred until after monomorphization, but the
--supporting tag and struct datatypes must be allocated here.
--I need to do that before bdt.field => *... because tagDT is a field!
--For boxed datatypes, tagDT is special in that it becomes a desugar of
--a tag pointer rather than a generated struct.

--Only defuns and globals contain exprs; they must be desugared.
--That involves allocating new code globals for strings and locals for
--let-based desugaring.
--It's clearer to do that only on the two relevant fields...
--But first, the un-desugared decls must be grouped.
--TODO: display all collisions and the associated definitions.

--DError-specific function
groupEx :: String -> (P.D -> (Name,v)) -> Map String [P.D] ->
  Either DError (Map Name v)
groupEx decltype sel decls =
  let ds = case M.lookup decltype decls of
             Just ds -> ds
             Nothing -> error $ "Compiler error: decls lacks " ++ decltype
  in groupExclusive sel ds ? Duplicate decltype
--Generic function
groupExclusive :: Ord k => (a -> (k,v)) -> [a] -> Either k (Map k v)
groupExclusive sel =
  foldM (\m a -> do
           let (k,v) = sel a
           complainIf (M.member k m) k
           return $ M.insert k v m) M.empty

groupGlobals = groupEx "Global" $
  \(P.Global gr vb) ->
    let (g,me) = collectVarBind vb
        r = desugarRegion gr
    in (g,(r,me))
groupDefuns di x = do
  nm2peps <- groupEx "Defun" 
    (\(P.Defun (Ident f) pe ps) -> (f,(pe,ps))) x
  let nmpeps = M.toList nm2peps
  M.fromList <$> mapM (\(f,(pe,ps)) -> do
                          p <- desugarP di pe
                          s <- desugarS di ps
                          return (f,(p,s))) nmpeps

--Instances are keyed by function name; it's fine for there to be multiple
--instances for a single name, they're just collected into a set.
--groupInstances is pure no longer; because it desugars immediately it can
--fail.
groupInstances :: DInfo -> [P.D] -> Either DError (Map Name (Set (T,Pat,S)))
groupInstances di ds =
  let kelems = [(fnm,(t,e,s)) | P.Instance (Ident fnm) t e s <- ds]
  in foldM (\m (fnm,(pt,pe,ps)) -> do 
              let t = desugarT pt
              p <- desugarP di pe
              s <- desugarS di ps
              return $ putElem fnm (t,p,s) m)
     M.empty kelems
  where putElem k elem m =
          case M.lookup k m of
            Nothing -> M.insert k (S.singleton elem) m
            Just elems -> M.insert k (S.insert elem elems) m
--Combine ordinary defuns and instances into a single map; they're mutex, so
--complain if their fnames intersect.
combineDefsAndInstances :: Map Name (Pat,S) ->
                           Map Name (Set (T,Pat,S)) ->
                           Either DError (Map Name
                                         (Either (Pat,S)
                                          (Set (T,Pat,S))))
combineDefsAndInstances ds is = do
  let fds = M.keysSet ds
      fis = M.keysSet is
      conflicts = S.intersection fds fis
  complainIf (not $ S.null conflicts)
    $ DefunInstanceOverlap conflicts
  return $ M.union (M.map Left ds) (M.map Right is)
  
collectVarBind :: P.VarBind -> (Name, Maybe P.E)
collectVarBind = \case
  P.JustVar (Ident v) -> (v, Nothing)
  P.VarIs (Ident v) e -> (v, Just e)
  
desugarRegion :: P.GlobalRegion -> Region
desugarRegion = read . take 2 . show
  
--This can't fail, so there's no need to make it a monad
desugarConArgs :: P.ConArgs -> (Name,[Name])
desugarConArgs = go
  where go = \case
          P.CANil (UIdent tycon) -> (tycon,[])
          P.CACons conlhs (Ident param) ->
            let (tycon,params) = go conlhs
            in (tycon,params++[param]) --I know it's quadratic...
