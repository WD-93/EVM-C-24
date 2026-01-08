{-# LANGUAGE LambdaCase #-}
module Fused where

import AST.DTs
import AST.Util (rollTyApps,unrollTyApps,freeTypedVarsPatList)
import qualified AST.DTs as A
import Const.Const
import Structured.DTs
import qualified Structured.DTs as IR
import Core.RestrictedCore
import Core.PrimTypes
import Mono.Mono (instT,bindT,BindError(..)) --TODO move, Mono is defunct
import Fused.Monad
import Construct (construct,dot)

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Except
import Control.Monad
import Data.List (elemIndex)

compileStructured :: Module -> Either FusedError Structured
compileStructured mod = do
  fs <- runExcept $
        flip execStateT initFusedS $
        flip runReaderT mod $
        runFusedM $
        compileStructuredM
  return $ fusedS2Structured mod fs
fusedS2Structured :: Module -> FusedS -> Structured
fusedS2Structured m fs = Structured {
  sdefuns = fsDefuns fs,
  --For code globals: Ptr Code t
  --For r globbals: Ptr r t
  --The Integer in state is pointless since global placement is
  --done later?
  sglobals = fsGlobals fs,
  stagSchemes = fsTagSchemes fs,
  sdtsInfo = dtsInfo m,
  ssizeof = fsSizeof fs
  }
compileStructuredM :: FusedM ()
compileStructuredM = do
  --First, find params for main that yield () -> ().
  (tyvars,polyt) <- do msig <- asks (M.lookup "main" . tysigs)
                       case msig of
                         --If main does not exist, error.
                         Nothing -> throwError NoMain
                         Just sig -> return sig
  --If no such params exist, error.
  v2t <- case bindT polyt (Unit :-> Unit) of
           Left bindErr -> throwError $ IlltypedMain bindErr polyt
           Right v2t -> return v2t
  --tyvars will contain all vs in v2t
  let params = map (\v ->
                      case M.lookup v v2t of
                        Nothing -> error "Compiler error: bad main sig"
                        Just t -> t) tyvars
  --Instantiate it with those params.
  --When rewriting to support library mode, will instead need to explore the
  --given exported functions.
  exploreF "main" params

--Converts the given monomorphic function to a Structured function.
--Idempotent, is a noop when repeated.
--First instantiates the function to a monomorphic definition; for class
--functions, an arbitrary instance with matching type is used.
--There may be no matching instances, in which case a NoInstance error is
--thrown.
--All functions, globals and datatypes the function depends on are
--recursively explored.
--TODO reuse code from Mono.Mono
exploreF :: Name -> [T] -> FusedM ()
exploreF f ts =
  idempotent fsVisitedFuns (\fs x->fs{fsVisitedFuns=x}) (f,ts) $ do
  mod <- ask
  def <- case M.lookup f $ defuns mod of
           Just def -> return def
           _ -> throwError $ GenericFE "Missing f in exploreF"
  (params,t) <- case M.lookup f $ tysigs mod of
                  Just sig -> return sig
                  _ -> throwError $ GenericFE "Missing sig in exploreF"
  --Assumption: length params == length ts
  let v2t = M.fromList $ zip params ts
      Right ft = instT v2t t --f@ts's monotype
  monoDef <- case def of
               --A normal defun:
               Left ps -> let Right ps' = instT v2t ps
                          in return ps'
               --A class function:
               --Find the first instance which matches
               Right tpsset ->
                 let tpss = S.toList tpsset
                 in instClass f ts ft tpss
  --Generate the Structured definition
  convertF f ts ft monoDef
    where
      instClass :: Name -> [T] -> T -> [(T,Pat,S)] -> FusedM (Pat,S)
      instClass f ts ft = \case
        [] -> throwError $ GenericFE $ "No instance for "++f++"@"++show ts
        (t,p,s):tpss ->
          case bindT t ft of
            Left _ -> instClass f ts ft tpss
            Right v2t -> let Right ps' = instT v2t (p,s)
                         in return ps'
--Generate the Structured definition of a given C function, store it in
--fsDefuns.
--Primfuns are handled in Core rather than Structured (which can only express
--normal return, not e.g. stop).
--Calling convention for a -> b:
--Type: Cont (a#1..a#n,Cont (b#..b#m,stk) Env,stk) Env
--where n, m is wordsize a, b
--LHS: (($arg.1..$arg.n,$ret,$stk),<env>)
--That also gives the initial scope.
--First declare every local in p, then match $arg with it and set the scope
--to the locals in order of occurrence.
--(x,y,z) patterns should have zero-overhead matching.
--Consequence: f(x,*x) := ... --the x in *x will eval to 0; exprs in patterns
--are fully evaluated before any matching is done.
convertF :: Name -> [T] -> T -> (Pat,S) -> FusedM ()
convertF f ts ft ps = do
  let flabel = mkLabel f ts
  --Generate structured definition
  sdef <- convertDef f ts ft ps
  modify (\fs -> fs{fsDefuns = M.insert flabel sdef $ fsDefuns fs})
convertDef :: Name -> [T] -> T -> (Pat,S) -> FusedM (BranchValue,[Stmt])
convertDef f ts ft@(a :-> b) (p,s) = do
  scope <- initialScope a b --triggers DT exploration
  ((),_ffs,stmts) <- unliftFFM (compileF f ts a b p s) (FFR (f,ts))
                     FFS {ffsScope = scope,
                           ffsInLoop = False
                         }
  return ((scope,Just $ Mono ("$stk") (TyVar "stk"), envV),stmts)
-- $arg.1..$arg.n,ret,stk
initialScope :: T -> T -> FusedM Scope
initialScope a b = do
  --Annoying... I should've implemented capab classes. TODO
  (arg,_,_) <- unliftFFM (localToVars a "$arg")
               (error "ignored") (error "ignored")
  wlen <- numWords b
  return $ arg ++ [Mono "$ret" (returnContT wlen b)]
  
compileF :: Name -> [T] -> T -> T -> Pat -> S -> FFM ()
compileF f ts a b p s = do
  --The last word is $ret
  scope <- getScope
  let arg = init scope
  --Mistake: freeVarsPatList returns [Name] rather than [(Name,Maybe T)]
  --I'll have to make a variant.
  let vts = freeTypedVarsPatList p
  --Each local is declared as null()
  z <- pushK 0
  localVars <- concat <$> mapM (\(nm,t) -> localToVars t nm) vts
  copyTo localVars $ replicate (length localVars) z
  --We need the vars on the stack now for pattern eval to work...
  --this will need to be optimized away.
  putScope $ localVars ++ scope
  --Eval the pattern p's exprs and assign the preexisting arg to it
  assignValue p arg
  --Generate the function body
  putScope localVars
  convertS s
  returnNull b

--Assigns vs to the given pattern
assignValue :: Pat -> [Var] -> FFM ()
assignValue p vs = do
  mep <- evaluatePat p
  case mep of
    Nothing -> return ()
    Just ep -> assignEP ep vs
--Consider the expression ptr[f()]++. To avoid repeating the side effect of
--f() and storing to a different address than was loaded from,
--it must be evaluated and bound to vars.
--EvaluatedPat replaces every expr in a Pat with its evaluated result.
--Nothing indicates a wildcard.
--The exprs may include function calls, so evaluatePat must modify scope.
--Note when the tag check is removed from the case Con {}, it becomes a
--wildcard.
--Argh, TODO support boxed cons.
evaluatePat :: Pat -> FFM (Maybe EvaluatedPat)
evaluatePat = go
  where go = \case
          PWild _ -> return Nothing
          PArray (Just a) ps -> do
            meps <- mapM go ps
            let ixeps = [(ix,ep) | (ix, Just ep) <- zip [0..] meps]
            if null ixeps
              then return Nothing
              else return $ Just $ EPArray (fromIntegral $ length ps) a ixeps
          PCon con (Just ts) fieldps -> do
            fieldmeps <- mapM (\(field,p) ->
                                 (,) field <$> go p) fieldps
            let fieldeps = [(field,ep) | (field, Just ep) <- fieldmeps]
            --Set checkTag if the datatype has >1 canonical constructor
            --(implies tag scheme /= Nil).
            mod <- liftFused ask
            let Just Con{conParent=tycon} =
                  M.lookup con $ conInfo $ dtsInfo mod
                Just DTInfo{dtCanonicalCons=cons} =
                  M.lookup tycon $ datatypes $ dtsInfo mod
                checkTag = length cons > 1
            --Explore con's datatype
            liftFused $ exploreD [] S.empty (tycon,ts)
            return $ epcon con ts checkTag fieldeps
--A smart constructor for Maybe EPCon
epcon :: Name -> [T] -> Bool -> [(Name,EvaluatedPat)] -> Maybe EvaluatedPat
epcon con ts checkTag fieldeps
  | not checkTag, null fieldeps = Nothing
  | let = Just $ EPCon con ts checkTag fieldeps
--p++ => ep <- evaluatePat p; x <- evalEP ep, assignEP ep (inc x)
--Do I also need to return a t?
--Note: does not modify the scope.
evalEP :: EvaluatedPat -> FFM [Var]
evalEP = error "todo"
--No assumption is made about the location of the EP vars or the rhs on the
--stack; they may be in either order depending on whether you assign via
--p = e or case e of {p => s}
assignEP :: EvaluatedPat -> [Var] -> FFM ()
assignEP = error "todo"
--Compilable pattern forms:
--local (.field | !ix)*
-- *p --all .field and !ixs have been rolled into the pointer
--Array (ix=>p) --wildcards omitted
--Con {field: p} --con tag check omitted in case
--Can I do the same for local that I do for *p? The issue is WordPad.
--local.field!ix where ix is outside the range of the field is UB
--(though I'll accept it without complaint for (*p).field!ix).
--A datatype with tag scheme Nil or only one constructor will never have its
--tag checked. Consequence: for datatype
--data Con = {Con}; tag Con = Array 4 Byte where {Con: "good"};
--Con = coerce "bad!" --will be accepted!
--EPCon Con ts False [] is equivalent to wild, so it's invalid.
--EParray _ _ [] is also invalid.
data EvaluatedPat = EPLocal Name T IndexPath
                  | EPDeref Var --a pointer
                  | EPArray Integer T --array len and elem type
                    [(Int,EvaluatedPat)] --non-wild indices in ascending order
                  | EPCon Name [T] --monomorphic con
                    Bool --must check tag
                    [(Name,EvaluatedPat)] --non-wild fields
  deriving (Eq,Ord,Read,Show)
type IndexPath = [Either (Name,[T]) --field
                  Var --index (Short)
                 ]

--Generates the code to return null. Huh, I actually don't need to make null
--a primitive: its code will be auto-generated given an empty body.
returnNull :: T -> FFM ()
returnNull t = do
  scope <- getScope --we only need $ret
  ret <- cNull t
  emitStmt $ IR.Return (ret ++ [last scope]) ret
--Inline null()
--I can't call it null, it collides with Prelude...
cNull :: T -> FFM [Var]
cNull t = do
  --It's better for opt purposes to copy a single var
  z <- pushK 0 -- :: Word
  ret <- newVars t
  copyTo ret $ replicate (length ret) z
  return ret

exploreG :: Name -> FusedM ()
exploreG g = idempotent fsVisitedGlobals (\fs x->fs{fsVisitedGlobals=x}) g $
             error "todo"

--Map monomorphic fields to offsets; that info is not required after
--Structured. Is sizeof used in post-Structured case compilation? Add it later
--if so.
--Given TyCon Ts, look up data TyCon ts = {Con {field: t}; ...} and monomorphize
--each field. If it has a non-Nil tag scheme (boxed has Nil), .tagTyCon has
--offset 0. For each con, each field has offset = sum of sizes of preceding
--fields (including tag if any).
--The DT's size is the maximum of each constructor's size.
--Takes a tycon stack :: [Name] to detect loops; tyconset = S.fromList tycons
--is used to accelerate cycle detection.
exploreD :: [Name] -> Set Name -> MonoT -> FusedM ()
exploreD tycons tyconset mt@(tycon,ts)
  | S.member tycon tyconset =
    throwError $ CyclicalDatatypes $ reverse $ tycon:tycons
  | let = idempotent fsVisitedDatatypes (\fs x->fs{fsVisitedDatatypes=x}) mt $
          do mod <- ask
             --TODO throw compiler error on DT missing
             let Just DTInfo{
                   dtParams = params,
                   dtTagScheme = tagScheme,
                   dtCanonicalCons = cons
                   } = M.lookup tycon $ datatypes $ dtsInfo mod
                 v2t = if length ts /= length params
                   then error "!!?"
                   else M.fromList $ zip params ts
             --If tag scheme is custom, each tag expr must be monomorphized and
             --serialized; don't support custom tags just yet...
             --or initializers in globals.
             (monoTagScheme,tagSz,mtagT) <-
               case tagScheme of
                 Nil -> return (Nil,0, Nothing)
                 N1 len -> return (N1 len,
                                   fromIntegral len,
                                   Just $ UInt $ fromIntegral len)
                 N16 -> return (N16, 1, Just $ UInt 1)
                 Custom t con2tag -> error "todo"
             --Store the monomorphized tag scheme
             modify (\fs->fs{fsTagSchemes = M.insert (tycon,ts)
                                            (cons,monoTagScheme) $
                                            fsTagSchemes fs
                            })
             --If tag scheme /= Nil, add .tagTyCon offset (0)
             case mtagT of
               Just tagT -> 
                 modify (\fs->fs{fsOffsets = M.insert ("tag"++tycon,ts)
                                  (0,tagSz,tagT) $
                                  fsOffsets fs
                                })
               Nothing -> return ()
             --Get the field names and types for each constructor
             --TODO throw compiler error if con missing
             fieldss <- forM cons (\con ->
                                     let Just Con{conFields = fields} =
                                           M.lookup con $ conInfo $ dtsInfo mod
                                     in return fields)
             --for each fields in fieldss:
             --for each field in fields:
             --its offset = the sum of sizes of preceding fields
             --We also return the total size
             conszs <- forM fieldss $ setFieldOffsets ts tagSz
             let dtSz = if not $ null conszs
                        then maximum conszs
                        else tagSz
             --Store the sizeof the DT
             modify (\fs->fs{fsSizeof = M.insert (tycon,ts) dtSz $
                              fsSizeof fs
                            })
               where setFieldOffsets ts off = \case
                       [] -> return off
                       (field,t):fields -> do
                         --Note we push tycon to the tycon stack in order to
                         --detect cyclical DTs
                         sz <- sizeof' (tycon:tycons)
                               (S.insert tycon tyconset) t
                         modify (\fs-> fs{fsOffsets = M.insert (field,ts)
                                           (off,sz,t) $
                                           fsOffsets fs
                                         })
                         setFieldOffsets ts (off+sz) fields
--nm is either a function or global; explore it.
exploreTyApp  :: Name -> [T] -> FusedM ()
exploreTyApp nm ts = do
  mod <- ask
  case () of
    _ | M.member nm $ globals mod, null ts -> spawnExploreG nm
      | M.member nm $ defuns mod -> spawnExploreF (nm,ts)
      | otherwise ->
        error $ "Compiler error in exploreTyApp: undefined "++nm++"@"++show ts

--Return the type of nm@ts
--TODO write instScheme, put it somewhere appropriate
typeTyApp :: Name -> [T] -> FusedM T
typeTyApp nm ts = do
  mod <- ask
  case M.lookup nm $ tysigs mod of
    Just (params,ty)
      | length params /= length ts ->
        error "Compiler error in typeTyApp: param len mismatch"
      | let -> let v2t = M.fromList $ zip params ts
                   Right t = instT v2t ty
               in return t
    _ -> error $ "Compiler error in typeTyApp: no tysig for " ++ nm
--The type of Con@ts {...} = TyCon ...ts
typeCon :: Name -> [T] -> FusedM T
typeCon con ts = do
  mod <- ask
  case M.lookup con $ conInfo $ dtsInfo mod of
    Just ci -> return $ unrollTyApps (TyCon $ conParent ci) ts
    _ -> error $ "Compiler error in typeCon: nonexistent con " ++ con

--Given a getter, setter and key, ensures an idempotent action is run only
--once for the given set and key.
idempotent :: Ord k =>
              (FusedS -> Set k) ->
              (FusedS -> Set k -> FusedS) ->
              k ->
              FusedM () ->
              FusedM ()
idempotent getter setter k m = do
  st <- get
  let ks = getter st --can't call it set, it would be confusing...
  if S.member k ks
    then return ()
    else put (setter st $ S.insert k ks) >> m

--Inspiration: Structured.Convert
--All statements but Declare reset scope.
--Naming convention: the nth word of the local x is x.n
--End result: locals will appear as x#n.m : W t m
convertS :: S -> FusedFunM ()
convertS (AST.DTs.Declare nmes) = mapM_ declare nmes
  where declare (x,e) = do
          scope <- getScope
          (vs,_t) <- convertE e
          --copy vs to x.1..n : W t 1..n
          let xs = [Mono (x++"."++show n) t | (n, Mono _ t) <- zip [1..] vs]
          copyTo xs vs
          putScope (xs ++ scope)
convertS s = cleanup $
  case s of
    SE e -> convertE e >> return ()
    A.Return e -> do
      (vs,t) <- convertE e
      scope <- getScope
      emitStmt $ IR.Return scope vs
    A.Ifte e th el -> do
      scope <- getScope
      (w,cond) <- collectCond scope e
      --The then and else branch have starting scope = scope
      ths <- block scope th
      els <- block scope el
      emitStmt $ IR.Ifte scope cond w ths els
    A.While e body -> do
      scope <- getScope
      (vs,cond) <- collectCond scope e
      bcode <- block scope body
      emitStmt $ IR.While scope cond vs bcode
    A.Case e cases -> do
      scope <- getScope
      --Need to eval e in scope (pushing it to the stack), then push its
      --tag as well.
      error "todo"
    --A stmt with higher scope (suffix) may safely follow one with lower; no
    --special construct is needed for blocks or block end in Structured.
    Block ss -> do
      scope <- getScope
      mapM_ convertS ss
      putScope scope
    A.Break -> getScope >>= (emitStmt . IR.Break)
    A.Continue -> getScope >>= (emitStmt . IR.Continue)
  where cleanup m = do
          scope <- getScope
          m
          putScope scope
--Evaluates an e in the given scope and applies truthy to it, returning the
--result and body.
collectCond :: Scope -> E -> FFM (Var,[Stmt])
collectCond scope e =
  collect scope $ do
  (vs,_t) <- convertE e
  truthy vs

--Invariants: if it returns (vs,t), length vs is the word length of t and
--the scope effect is (vs++).
convertE :: E -> FFM ([Var],T)
convertE e = pushScope $ go e
  where go = \case
          EInteger n -> do
            w <- pushK n
            return ([w], UInt 32)
          --A local variable; find its wordlen n, then result = copy
          --x.1 .. x.n
          --Not copying would lead to a subtle bug:
          --var y = x;
          --x++ //would be visible in y
          TypedVar (Just t) x -> do
            xs <- localToVars t x
            ys <- copyVars xs
            return (ys,t)
          --Push f, push x, call f x
          f :$ x -> do
            (fs,a2b) <- convertE f
            let [fv] = fs
                a :-> b = a2b
            (xs,_) <- convertE x
            scope <- getScope --will be xs++fs++original scope
            res <- newVars b
            emitStmt $ Call scope res fv xs
            return (res,b)
          -- ::: eliminated in HM
          p A.:= e -> error "todo"
          --Eval es in textual order, reverse and concat
          --Need to optimize to avoid dups and swaps out of range... eagerly
          --shift and or, CE.
          EArray (Just t) es -> error "todo"
          --Either g or f; either way push a 2B label.
          --Storing only typarams and not the type in TyApp was a mistake...
          --To get type: fetch scheme from tysigs, instantiate.
          TyApp nm ts -> do
            liftFused $ exploreTyApp nm ts
            t <- liftFused $ typeTyApp nm ts
            w <- pushLabel2 nm ts t
            return ([w],t)
          --caseE not supported yet
          --CaseE e cases -> error "todo"
          --What is the me for again?
          OPAssign me p op e -> error "todo"
          --PPPre et al mostly the same
          --Special case: WordPad {unWordPad: e} has zero runtime overhead.
          ConRecord "WordPad" (Just [a]) [("unWordPad",e)] -> do
            (vs,_a) <- convertE e
            res <- newVars $ WordPad a
            copyTo res vs
            return (res, WordPad a)
          --All Con {} with tag scheme nil are null(), but that can be achieved
          --via constant expansion anyway.
          --Standard:
          --eval fields, concat with tag if any, stitch in canonical field order
          --default value if field missing: 0
          --Need opts to shift/or eagerly to avoid blowing up the stack.
          --Note boxed con Es have been desugared away.
          ConRecord con (Just ts) field_es -> do
            --Should I just return the sizeof the tag here?
            (ser,tagT) <- liftFused $ getTag con ts
            tagSz <- liftFused $ sizeof tagT
            --TODO double-check repeated fields have already been ruled out.
            field2vs <- M.fromList <$> forM field_es (\(field,e) -> do
                                                         vs <- convertE e
                                                         return (field,vs))
            tag <- pushMultiWordSer ser tagT --May be 0 or >1 words
            --If the constructor has tag scheme Nil, tag will be 0 words
            resT <- liftFused $ typeCon con ts --TyCon ts
            res <- constructCon con ts tag tagSz field2vs resT
            return (res,resT)
          --Boxed fields have been desugared away.
          --For now, I make no use of padding info: the entire field is assumed
          --to be potentially nonzero, as is the rest of the struct.
          Dot e (Just ts) field -> do
            (vs,tycon_ts) <- convertE e
            let (TyCon tycon, _ts) = rollTyApps tycon_ts
            --mono dt
            szStruct <- liftFused $ sizeof tycon_ts
            --the field has a type t and size sz
            (off,szField,t) <- liftFused $ getFieldInfo field ts
            if szField == 0
              --The field is zero-sized; dot is trivial
              then return ([],t)
              else do
              --Select the words containing the field
              --Note off is the offset of the field from the left in memory;
              --on the stack there may be additional left-padding.
              let leftPad = (szStruct `roundedUpMod` 32) - szStruct
                  stackOff = leftPad + off
                  startIx = stackOff `div` 32
                  endIx = (stackOff + szStruct - 1) `div` 32
                  relVs = drop (fromInteger startIx) $
                          take (fromInteger $ endIx-startIx+1) vs
                  --right-offset mod 32
                  rightOff = (szStruct - off - szField + 1) `mod` 32
                  --Output words = disjunction (input << +-k)
                  wshifts = dot (fromIntegral rightOff)
                            (fromIntegral szField) relVs
              --The leftmost input word containing the field may also have
              --garbage to the left of it; mask it out.
              let whd:wtl = wshifts
                  (top,sh):wrest = whd
                  garb = stackOff `mod` 32
              vtop <-
                if garb == 0
                then top <<< sh --no need to shift out garbage
                else if sh > 0
                     then (top <<< garb) >>= (<<< (fromIntegral sh - garb))
                          --shift out garbage, then shift back
                     else maskBytes (32-garb) top
                          --can't use shift trick, must use code-intensive
                          --and 0xff... instead.
              vrest <- forM wrest (\(v,sh) -> v <<< sh)
              vhd <- disjunction $ vtop:vrest
              vtl <- (forM wtl (\wshs ->
                                 forM wshs (\(w,sh) -> w <<< sh)))
                     >>= mapM disjunction
              return (vhd:vtl, t)
        pushScope :: FFM ([Var],T) -> FFM ([Var],T)
        pushScope m = do
          scope <- getScope
          (vs,t) <- m
          putScope $ vs ++ scope
          return (vs,t)

--Get off, sz, t of .field@ts; errors if the datatype has not been explored.
getFieldInfo :: Name -> [T] -> FusedM (Integer, Integer, T)
getFieldInfo field ts = do
  s <- get
  case M.lookup (field,ts) $ fsOffsets s of
    Just x -> return x
    Nothing -> throwError $ CompilerErrorFieldInfoBeforeExploreD field ts

--TODO place helpers in sensible order
--Gets the serialized constructor tag (a single, potentially multi-word
--bytestring).
--Returns the empty Serialized if the datatype has tag scheme Nil or a custom
--zero-sized tag; currently doesn't handle custom.
getTag :: Name -> [T] -> FusedM (Serialized,T)
getTag con ts = do
  --TODO turn into combinator...
  mod <- ask
  let dtsi = dtsInfo mod
      Just Con{conParent=tycon} = M.lookup con $ conInfo dtsi
      Just DTInfo{dtTagScheme = tagScheme,
                  dtCanonicalCons = cons
                 } = M.lookup tycon $ datatypes dtsi
  exploreD [] S.empty (tycon,ts)
  --Will fail for a boxed constructor...
  let Just conIx = elemIndex con cons
  return $ case tagScheme of
             Nil -> (emptySer, TyCon "Unit")
             Custom {} -> error "todo custom tag schemes in getTag"
             N1 len ->
               --TODO make a combinator for Serialized from serInt...
               let leni = fromIntegral len
               in (Serialized {
                      serLength = leni,
                      serSizeof = leni,
                      serContent = 
                          [Left $ serInt leni $ fromIntegral conIx]
                      },
                    UInt leni)
             N16 -> (Serialized {
                        serLength = 1,
                        serSizeof = 1,
                        serContent = 
                            [Left $ serInt 1 $ fromIntegral conIx]
                        },
                      UInt 1)

--Concat tag and fields in canonical order;
--same procedure as for array construction.
--FW opt: use knowledge about zero bytes in the element types to avoid
--stitching work.
--Ex: Struct (WordPad Short, Short) --that's two words on the stack, but the
--top word is always 0 because it only contains two padding bytes from
--WordPad Short. That's solved by symbolic eval opt...
--What info do I need? Just the var lists and their offsets + the total size.
constructCon :: Name -> [T] -> [Var] ->
                Integer -> Map Name ([Var], T) -> T ->
                FusedFunM [Var]
constructCon con ts tag tagSz field2vst resT = do
  sz <- liftFused $ sizeof resT
  --Look up fields of con and their offsets
  fields <- do
    mod <- liftFused ask
    let cis = conInfo $ dtsInfo mod
        Just ci = M.lookup con cis
    return $ map fst $ conFields ci
  --Argh: the tag also needs a size and right-offset.
  let tagOff = sz - tagSz
  --For field in fields:
  offLenVs <- (((fromInteger tagOff, fromInteger tagSz,tag):) <$>
              forM fields (\field -> do
                              (off,len,t) <- liftFused $ getFieldInfo field ts
                              let rightOff = sz-off-len
                              vs <-  case M.lookup field field2vst of
                                       --Field is present
                                       Just (vs,_t) -> return vs
                                       --Default if absent: null()
                                       --cNull redundantly gets t's wordsize;
                                       --I could use len instead.
                                       Nothing -> cNull t
                              return (fromInteger rightOff,
                                      fromInteger len,vs)
                          )) :: FFM [(Int,Int,[Var])]
  --For each output word, a list (input,sh) to or together
  let wshss = construct (fromIntegral sz) offLenVs
  mapM (\wshs -> (mapM (uncurry (<<<)) wshs) >>= disjunction) wshss
--Problem: we have n bytestrings represented as words on the stack.
--Each bytestring has a length and is right-aligned in the words.
--IOW, a bs with length len will have an offset of (-len)%32 bytes in its
--word repr.
--They must be concatenated into the same representation, consisting of
--ceil(totalBytes/32) words. Their left-offset into the output bytestring is
--given.
--Each of those output words is the disjunction of shifted input words.
--Solution: a module (again). TODO look up the old module.

--TODO reuse at the other location I use "."
localToVars :: T -> Name -> FFM [Var]
localToVars t x = do
  wlen <- liftFused $ numWords t
  return [Mono (x++"."++show n) t | n <- [1..wlen]]

--These must be here because they trigger DT exploration; Fused.Monad is for
--basic stuff.
--Generates new vars with the given C type
newVars :: T -> FFM [Var]
newVars t = do
  wlen <- liftFused $ numWords t
  mapM newVar [W t $ TyNat n | n <- [1..wlen]]
--Explore the given monomorphic t, then return its size
--sizeof called as part of datatype exploration needs to check for cycles,
--but the stack of tycons is always empty when exploring a function or
--global. Consequence: we need two sizeof variants.
--sizeof for f, g:
sizeof :: T -> FusedM Integer
sizeof = sizeof' [] S.empty
--sizeof for D
sizeof' :: [Name] -> Set Name -> T -> FusedM Integer
sizeof' tycons tyconset t = do
  let (TyCon tycon, ts) = rollTyApps t
  exploreD tycons tyconset (tycon,ts)
  sizes <- gets fsSizeof
  case M.lookup (tycon,ts) sizes of
    Nothing -> error "!?"
    Just sz -> return sz
--Used only in function compilation since it needs to deal with the stack
numWords :: T -> FusedM Integer
numWords t = ((`div` 32) . (`roundedUpMod` 32)) <$> sizeof t

--Inline disjunction of the given word vars using the OR opcode
--If the vars are empty, returns the identify of OR: 0.
truthy :: [Var] -> FusedFunM Var
truthy [] = pushK 0
truthy ws = go ws
  where go = \case
          --Copy rather than reuse avoids a scope where several vars with
          --the same name are on the stack.
          --Also, the result should be coerced to a Word...
          [w] -> copy (W (UInt 32) 1) w
          w1:w2:ws -> do
            w <- op2 "or" w1 w2
            truthy $ w:ws

--Collect the stmts of a block, isolating the writer effect and resetting the
--scope.
block :: Scope -> S -> FFM [Stmt]
block scope s = snd <$> collect scope (convertS s)
--Ditto but more general.
collect :: Scope -> FFM a -> FFM (a,[Stmt])
collect scope ffm = do
  cache <- getScope
  pass $ do
    putScope scope
    (a,stmts) <- listen ffm --collect the emitted stmts
    putScope cache
    return ((a,stmts), const []) --intercept them

-------------------------------------------------------------------------------
--Typechecked module =>
--f@ts => structured IR
--non-code g => offset
--code g => serialization
--monoT => sizeof
--con => serialized tag
--field => offset
--Incrementally cache DT info, recomputing Append, WordPad, Int, Ptr rather
--than caching them (?)
--I'll include type annots in Vars as before; they're required to distinguish
--State vars from words.

--Given an f@monoTs:
--Substitute tyvar[i] for monoTs[i].
--Generate structured IR:
--Get wordcount of argument, initial scope = $arg1..$argN,$ret
--Declare lhs vars; match lhs with $arg; scope = lhs vars.
--Generate the given stmt.
--SE e => vs <- generate e
--Return e => vs <- generate e; emit $ Return $ret:vs
--Ifte e th el => w <- generate (truthy e); sth <- isolate th; sel <- isolate el
-- emit $ Ifte w sth sel
--While similar, except e is isolated
--Case e cases => vs <- e; compileCase cases vs
--Case is complex: patterns may be fallible or infallible, boxed or unboxed,
--tag scheme varies. Drop all cases after the first infallible one.
--No infallible case => revert as default
--Otherwise => infallible case as default
--Only one case: equivalent to block
--Core needs in-code JT support for N1.
--Block: trivial
--Break, continue: trivial
--Declare v_es: why do the vars not include type...?

--Lookup special compilation schemes for primfuns: Map Name ([T] -> m ...)

--E:
--k: pushK k
--g: explore g >>= push
-- Non-code g becomes a push0,1 or 2; code gs become a push2 label
--addressOf *e: special case
--f :$ x => vf <- go f; vsx <- go x; emit $ Call vf vsx
--p := e => vs <- go e; assign p vs;
--EArray: eval all subexprs in order, concatenate them
--f@ts: explore f@ts >>= push
--caseE => don't support yet...
--p += k => vs <- eval p, p(vs) = k + p(vs)
--(++) etc: similar
--WordPad@[a] {unWordPad: e}: copy
--Con@ts fs => explore TyCon ts, eval fields in textual order, concat,
--prepend tag if any.
--e.field: look up sizeof e, offset and size of field, slice.
--Slice opts: data is leftmost excluding padding or rightmost.

--Patterns containing es must be evaluated on assignment. In non-default cases
--the top-level tag check is omitted.
--Assign: vs => ()
--_ = vs => pass
--local => copy op --omit copy in Core?
-- *p = vs => writePtr p vs --Convert (*p).field* => *p' first
--Define an indexArrayPtr primitive for PBang?
--Pointer overflows or underflows are UB, creating corrupt values on stack.
--PArray trivial; PCon may require tag check
--PDot requires unfolding, special treatment of unWordPad.

--Explore g: if const in cache, return it
--If non-code: set to current region offset, bump region offset by sz
--If code: serialize initializer, return label
--Don't support allocValue in serialize for now.

--Explore DT@ts: special-case WordPad.
--Serialize tags per con if any
--Compute sizeof + offsets per field
--Allow g, &(p->field)... and *codeG?
--Need to support indexPtr, offsetPtr. Allow label+k in consts?
