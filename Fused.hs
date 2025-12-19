{-# LANGUAGE LambdaCase #-}
module Fused where

import AST.DTs
import AST.Util (unrollTyApps)
import qualified AST.DTs as A
import Const.Const
import Structured.DTs
import qualified Structured.DTs as IR
import Core.RestrictedCore
import Core.PrimTypes
import Mono.Mono (instT,bindT,BindError(..)) --TODO move, Mono is defunct
import Fused.Monad

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Except
import Control.Monad

compileStructured :: Module -> Either FusedError Structured
compileStructured mod =
  fusedS2Structured <$> (runExcept $
                          flip execStateT initFusedS $
                          flip runReaderT mod $
                          runFusedM $
                          compileStructuredM)
fusedS2Structured :: FusedS -> Structured
fusedS2Structured = error "todo"
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
convertF :: Name -> [T] -> T -> (Pat,S) -> FusedM ()
convertF f ts ft = do
  let funvar = FPoly f ts ft
  error "todo"

exploreG :: Name -> FusedM ()
exploreG g = idempotent fsVisitedGlobals (\fs x->fs{fsVisitedGlobals=x}) g $
             error "todo"

exploreD :: MonoT -> FusedM ()
exploreD mt = idempotent fsVisitedDatatypes (\fs x->fs{fsVisitedDatatypes=x})mt$
              error "todo"

--nm is either a function or global; explore it.
exploreTyApp  :: Name -> [T] -> FusedM ()
exploreTyApp nm ts = do
  mod <- ask
  case () of
    _ | M.member nm $ globals mod, null ts -> exploreG nm
      | M.member nm $ defuns mod -> exploreF nm ts
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
          ConRecord con (Just ts) field_es -> do
            (ser,t) <- liftFused $ getTag con ts
            --TODO double-check repeated fields have already been ruled out.
            field2vs <- M.fromList <$> forM field_es (\(field,e) -> do
                                                         vs <- convertE e
                                                         return (field,vs))
            tag <- pushMultiWordSer ser t --May be 0 or >1 words
            --If the constructor has tag scheme Nil, tag will be 0 words
            t <- liftFused $ typeCon con ts --TyCon ts
            res <- constructCon con ts tag field2vs
            return (res,t)
          Dot e (Just ts) field -> error "todo"
        pushScope :: FFM ([Var],T) -> FFM ([Var],T)
        pushScope m = do
          scope <- getScope
          (vs,t) <- m
          putScope $ vs ++ scope
          return (vs,t)

--TODO place helpers in sensible order
--Gets the serialized constructor tag (a single, potentially multi-word
--bytestring).
getTag :: Name -> [T] -> FusedM (Serialized,T)
getTag = error "todo"

--Concat tag and fields in canonical order;
--same procedure as for array construction.
--FW opt: use knowledge about zero bytes in the element types to avoid
--stitching work.
--Ex: Struct(WordPad Short, Short) --that's two words on the stack, but the
--top word is always 0 because it only contains two padding bytes from
--WordPad Short.
constructCon :: Name -> [T] -> [Var] ->
                Map Name ([Var], T) -> FusedFunM [Var]
constructCon con ts = error "todo"

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
sizeof :: T -> FusedM Integer
sizeof = error "todo"
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
