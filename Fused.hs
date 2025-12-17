module Fused where

import AST.DTs
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
exploreF f ts = idempotent fsVisitedFuns (\fs x->fs{fsVisitedFuns=x}) (f,ts) $
                error "todo"

exploreG :: Name -> FusedM ()
exploreG g = idempotent fsVisitedGlobals (\fs x->fs{fsVisitedGlobals=x}) g $
             error "todo"

exploreD :: MonoT -> FusedM ()
exploreD mt = idempotent fsVisitedDatatypes (\fs x->fs{fsVisitedDatatypes=x})mt$
              error "todo"

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
      emitStmt $ IR.Return vs
    A.Ifte e th el -> do
      scope <- getScope
      (vs,_t) <- convertE e
      w <- truthy vs
      --The then and else branch have starting scope = scope
      ths <- block scope th
      els <- block scope el
      putScope $ w:scope
      emitStmt $ IR.Ifte w ths els
    A.While e body -> error "todo"
    A.Case e cases -> error "todo"
    Block ss -> error "todo"
    A.Break -> error "todo"
    A.Continue -> error "todo"
  where cleanup m = do
          scope <- getScope
          m
          putScope scope
convertE :: E -> FusedFunM ([Var],T)
convertE = error "todo"

--Inline disjunction of the given word vars using the OR opcode
--If the vars are empty, returns the identify of OR: 0.
truthy :: [Var] -> FusedFunM Var
truthy [] = pushK 0
truthy ws = go w ws
  where go ws = \case
          --Copy rather than reuse avoids a scope where several vars with
          --the same name are on the stack.
          --Also, the result should be coerced to a Word...
          [w] -> copy (W (UInt 32) 1) w
          w1:w2:ws -> do
            w <- op2 "or" w1 w2
            truthy $ w:ws

--Collect the stmts of a block, isolating the writer effect and resetting the
--scope.
block :: [Var] -> S -> FFM [Stmt]
block = error "todo"

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
