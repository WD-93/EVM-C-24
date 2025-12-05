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
import AST.Util (rollTyApps,mkSig,kindIsConcrete)
import qualified DeclBucket as DB 
import Import (PreModule(..),PMDynamicThing(..),MNL(..))
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

--DeclBucket now takes care of most of the conflict elimination.
--Remaining: tag clash on BDT + tag of ImplTyCon.
--Rules: only memory and code globals may have initializers.
--Should I drop memory initializers? They complicate trueMain and make
--init ordering non-obvious. The inits hint the type... but I can do that
--with an explicit type signature.
--Drop for now, verbose but obvious > terse but obscure.

desugar :: PreModule -> Either DError Module
desugar pm = do
  let tsigs = M.map mkSig $ getTs pmTySigs
      --pmKindSigs contains two types of decl: TyCon : T and TyCon : Kind;
      --the former become kindsigs, the set of keys in the latter become
      --kinds. Note type Foo = Kind; TyCon : Foo will not be recognized as
      --a kind declaration; the rhs must be syntactically Kind.
      kss = getTs pmKindSigs
      ksigs = M.filter (/= TyCon "Kind") kss
      ks = M.keysSet $ M.filter (== TyCon "Kind") kss
      dflts = getTs pmDefaults
      sthings = M.map fst $ pmStatThings pm --discarding location
      tsyns = M.mapMaybe (\case DB.STTySyn lnms pt ->
                                  Just (map fst lnms, desugarT pt)
                                _ -> Nothing) sthings
      --Now I need to desugar defuns, globals and dtsInfo
      --Perform as many context-dependent rewrites as possible in separate
      --traversals of the Module rather than baked into SEP desugaring.
      dthings = pmDynThings pm
      --The map of boxed fields => their tycon is still essential.
  --I need to add tags to pmFields here and error on conflict.
  --That unfortunately duplicates some of the logic from tag scheme inference
  --in processDTs.
  fieldsWithTags <- addTags (M.map fst $ pmFields pm)
                    (M.keysSet $ pmTagTypes pm) sthings
  --There are now two types of boxed field that desugaring needs to care about:
  --tag and normal; each has its own desugaring treatment.
  let di = DInfo {
        diFields = fieldsWithTags,
        diConFields = M.map (map (fst.fst) . DB.ciFields . fst) $
                      pmConstructors pm
        }
  gs <- mapM (\(r,mpe) ->
                (,) r <$> case mpe of
                            Nothing -> return Nothing
                            Just pe -> Just <$> desugarE di pe) $
        M.mapMaybe (\case PMGlobal (r_mpe,_loc) -> Just r_mpe
                          _ -> Nothing) dthings
  --TODO require each class fun has a tysig
  --Do I already require each tysig corresponds to a dynthing
  --and kindsig corresponds to a DT respectively?
  fs <- mapM (\case Left (pe,ps) -> Left <$>
                                    ((,) <$> desugarP di pe <*> desugarS di ps)
                    Right tess ->
                      --Quirk: syntactically identical instances will be
                      --merged since location info is removed. That will
                      --change as I propagate locs into the AST.
                      (Right . S.fromList) <$>
                      mapM (\(pt,pe,ps) -> do
                               p <- desugarP di pe
                               s <- desugarS di ps
                               return (desugarT pt, p, s)
                           ) (S.toList tess)) $
        --M.filter would be more succinct, but it's good practice to constrain
        --repr as early as possible.
        M.mapMaybe (\case PMDefun (e_s,_loc) -> Just $ Left e_s
                          PMInstances ltess -> Just $ Right $ S.map fst ltess
                          _ -> Nothing) dthings
  (dtsi,defaultDTKinds) <- processDTs di pm
  --The module on which context-dependent desugaring will be performed
  let mod = Module{
        tysigs = tsigs,
        kindsigs = M.union defaultDTKinds ksigs,
        kinds = ks,
        defaults = dflts,
        tysyns = tsyns,
        globals = gs,
        defuns = fs,
        dtsInfo = dtsi
        }
  --Rules:
  enforceRules mod
  --Time to apply context-dependent generic transformations:
  contextDependentDesugar mod
    where getTs field = M.map (\(pt,_loc) -> desugarT pt) $ field pm

--For each DT in sthings:
--If it is boxed, it has a boxed tag iff it has a tag decl or its ImplDT
--has a tag.
--If it is unboxed, it has a boxed tag iff it has a tag decl or >1 constructor.
--No, the type checker expects no BDTs have tags. To add .tagList I'll need
--to modify the TC.
addTags :: Map Name DB.FieldInfo -> Set Name -> Map Name DB.StaticThing ->
  Either DError (Map Name FieldInfo)
addTags fs tagged sthings = do
  let fi = M.map (\case DB.IsTag a (b,_) -> IsTag a b
                        DB.IsNormal a (b,_) (c,_) -> IsNormal a b c) fs
  --DT info
  let di = M.mapMaybe (\case DB.STDatatype _params cons Nothing ->
                               Just $ length cons
                             _ -> Nothing) sthings
        {-
      lookupImplDT tycon =
        case M.lookup ("Impl"++tycon) di of
          Nothing -> error "Eh!?"
          Just (len,_) -> if (("Impl"++tycon) `elem` tagged) || len > 1
                          then Just $ IsTag {fiBoxed = True,
                                             fiParentTyCon = tycon
                                            }
                          else Nothing-}
      tagFields = M.mapKeys ("tag"++) $ M.mapMaybeWithKey
                  (\tycon len ->
                      if (tycon `elem` tagged) || len > 1
                      then Just $ IsTag {fiBoxed = False,
                                         fiParentTyCon = tycon
                                        }
                      else Nothing) di
  reportOffenders NormalFieldsClashWithTags $
    S.intersection (M.keysSet fi) $ M.keysSet tagFields
  return $ M.union tagFields fi

--A collection of simple restrictions on modules
--1) All tysigs must correspond to a fun or global
--2) All class functions must have a tysig
--3) All concrete kind sigs must correspond to a DT
--4) Code globals must have initializers; other regions must not.
--5) All defaults must refer to an existing kind.
--6) No TyCon may be both declared as a root kind (Region, Nat, Type etc)
--   and given a kind signature (e.g. Type -> Type).
enforceRules :: Module -> Either DError ()
enforceRules mod = do
  --1) All tysigs must correspond to a fun or global
  let nakedTySigs = S.filter (\k -> not $
                                    M.member k (defuns mod) ||
                                    M.member k (globals mod)
                             ) $
                    M.keysSet $ tysigs mod
  reportOffenders TypeSignaturesLackBindings nakedTySigs
  --2) All class functions must have a tysig
  let nakedClasses = S.filter (\k -> not $ M.member k (tysigs mod)) $
                     M.keysSet $ M.filter (\case Right _ -> True
                                                 _ -> False) $ defuns mod
  reportOffenders ClassFunctionsLackSignatures nakedClasses
  --3) All concrete kind sigs must correspond to a DT
  let nakedKindSigs = S.filter (\k -> not $ M.member k $
                                      datatypes $ dtsInfo mod) $
                      M.keysSet $ M.filter kindIsConcrete $ kindsigs mod
  reportOffenders ConcreteKindSigsLackDTs nakedKindSigs
  --4) Code globals must have initializers; other regions must not.
  let uinitCodeGlobals = M.keysSet $ M.filter (\case (Co,Nothing) -> True
                                                     _ -> False) $ globals mod
  reportOffenders CodeGlobalsMustHaveInitializers uinitCodeGlobals
  let initOtherGlobals = M.mapMaybe (\case (r,Just _) ->
                                             if r /= Co
                                             then Just r
                                             else Nothing
                                           _ -> Nothing)
                         $ globals mod
  complainIf (not $ M.null initOtherGlobals)
    $ MustNotHaveInitializers initOtherGlobals
  --5) All defaults must refer to an existing kind.
  reportOffenders DefaultsMustReferToKinds $
    M.keysSet (defaults mod) `S.difference` kinds mod
  --6) No TyCon may be both declared as a root kind (Region, Nat, Type etc)
  --   and given a kind signature (e.g. Type -> Type).
  reportOffenders KindDeclKindSigCollisions $
    M.keysSet (kindsigs mod) `S.intersection` kinds mod
reportOffenders :: (Set a -> err) -> Set a -> Either err ()
reportOffenders err s = complainIf (not $ S.null s) $ err s

--1) g => *g in E and Pat
--2) Constructor desugaring
--a) Underapplied cons and overapplied pcons are handled in SEP
--b) Pair a b => Append {first:WordPad a, second:WordPad b} handled in SEP
--c) Con a1..aN => Con {field1:a1 .. fieldN:aN} handled in SEP
--d) BCon fs => ImplTyCon (allocValue (ImplBCon implTyCon_fs))
--3) Pair field desugaring: .fst => .first.unWordPad, .snd => .second.unWordPad
substGlobals :: Module -> Module
substGlobals mod =
  everywhere (mkT $ \case PVar v
                            | isGlobal v -> Deref Nothing $ Var v
                          p -> p) $
  everywhere (mkT $ \case Var v
                            | isGlobal v -> Var "deref" :$ Var v
                          e -> e)
  mod
  where isGlobal v = M.member v $ globals mod
--bdt.field has already been converted to *(bdt.unImplTyCon).implTyCon_field
--Undefined cons and bad fields should've already been caught.
--Pair {fst: a, snd: b} records should've been converted to Appends.
boxedConDesugaring :: Module -> Module
boxedConDesugaring mod =
  everywhere (mkT $ \case
                 e@(ConRecord con _ field_es) ->
                   let dtsi = dtsInfo mod
                       cis = conInfo dtsi
                   in case M.lookup con cis of
                        Nothing ->
                          error $ "No con info for " ++ con
                        Just ci ->
                          if conBoxed ci
                          then let tycon = conParent ci
                               in ConRecord ("Impl"++tycon) Nothing
                                  [("unImpl"++tycon,
                                    Var "allocValue" :$
                                    ConRecord ("Impl"++con) Nothing
                                    (map ((("impl"++tycon++"_")++)***id)
                                     field_es))]
                          else e
                 e -> e
             )
  mod
pairFieldDesugaring :: Module -> Module
pairFieldDesugaring mod =
  everywhere (mkT $ \case Dot e _ f
                            | f `elem` ["fst","snd"] ->
                              Dot (Dot e Nothing (extend f)) Nothing
                              "unWordPad"
                          e -> e) $
  everywhere (mkT $ \case p :. f
                            | f `elem` ["fst","snd"] ->
                              (p :. extend f) :. "unWordPad"
                          p -> p) mod
  where extend = \case
          "fst" -> "first"
          _ -> "second"
--I'll keep it an Either in case more rewrites need to be added.
contextDependentDesugar :: Module -> Either DError Module
contextDependentDesugar mod =
  return $ boxedConDesugaring $ pairFieldDesugaring $ substGlobals mod

{-

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
      di = DInfo {diGlobalSet = gset,
                  diDTsInfo = dtsFull,
                  diStringNumbering = string2n
                 }
  dtsFinal <- sepDTs di dtsFull
  --Also add string globals to global map
  gsFinal <- M.union (stringGlobals string2n) <$> sepGlobals di gs
  let gsetFinal = M.keysSet gsFinal
  -- ^ gotta include the string globals to prevent TypeSignaturesLackBindings
  --default
  dflts <- groupEx "Default" (\(P.Default (UIdent nm) t) -> (nm, desugarT t))
    nm2d
  --tysig
  --tysigs also need string global tysigs inserted to fix their type
  tsigs <- M.union (stringTySigs string2n) <$>
    groupEx "TySig" (\(P.TySig (Ident nm) t) -> (nm, mkSig $ desugarT t)) nm2d
  
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
     let nakedSigs = S.difference sigs (S.union fset gsetFinal)
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
                       map ((Var "fromWord" :$) . EInteger . fromIntegral . ord)
                       str))) $
  M.toList string2n
--Strings are also of a fixed type: Array len Byte
--TODO fuse the functions if it matters to perf...
stringTySigs :: Map String Int -> Map Name ([Name],T)
stringTySigs string2n =
  M.fromList $
  map (\(str,n) -> ("$string" ++ show n, (,) [] $ --the scheme takes no params
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

-}
