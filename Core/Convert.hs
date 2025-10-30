{-# LANGUAGE PatternSynonyms #-}
module Core.Convert where

import AST.DTs (T(..),Name(..),tupleT)
import qualified AST.DTs as T (pattern Pair)
import Structured.DTs
import Core.RestrictedCore

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

--Takes a Structured module and produces a pre-SSA Core module
--Invariant: every Structured stmt other than Declare is preceded by a
--Declare.
structured2core :: Structured -> Either CoreError Core
structured2core smod = do
  --Convert each Structured function to a BB map, then union them
  let defs = M.toList $ sdefuns smod
  bbmaps <- mapM (\(fv,(p,body)) -> coreF fv p body) defs
  return Core {coreDefuns = M.unions bbmaps,
               coreGlobals = sglobals smod,
               coreStatic = sstatic smod
              }

--No need for break/continue outside loop, it's caught in Structured.
data CoreError = CEPlaceholder
  deriving (Eq,Ord,Read,Show)
{-
State:
loops: [(fcont,scope),(fbreak,scope)]
ops accumulated so far
current Core function being accumulated
-}
type Cont = (FunVar,Scope)
type Scope = [Var]
data CoreS = CoreS {
  csAllocCtr :: Int, --for allocating new function names
  csLoopStack :: [(Cont,Cont)],
  csCurrentFun :: (FunVar,Pattern),
  csOps :: [(Value,OpE)], --accumulated ops in reverse order
  --The BB map; on a branch the current fun and its ops are flushed to the
  --map.
  csDefuns :: Map FunVar (Pattern,[(Value,OpE)],Branch)
  }
  deriving (Eq,Ord,Read,Show)
--The monad for accumulating the CFG of a single Structured function.
type CoreM = ReaderT FunVar --parent fun; is source module needed?
             (StateT CoreS (Except CoreError))

--Converts a single Structured function to a map of BBs
--Function blocks have an implicit return null() next.
--It's safe for it to just have $ret in its scope.
--It's fine to reset the alloc counter for each coreF; each anon BB's name will
--also be pased on the parent function.
coreF :: FunVar -> Pattern -> [Stmt] ->
  Either CoreError (Map FunVar (Pattern,[(Value,OpE)],Branch))
coreF fv p body =
  fmap csDefuns $ runExcept $ flip execStateT initSt $
  flip runReaderT fv $ do
  (rn,rnp) <- newFunLHS' "returnNull" [Mono "$ret" $ error "todo"]
  error "todo"
  where initSt = CoreS {
          csAllocCtr = 1,
          csLoopStack = [],
          csCurrentFun = (fv,p),
          csOps = [],
          csDefuns = M.empty
          }

coreBlock :: [Stmt] -> --remaining stmts
             Cont -> --next cont
             CoreM ()
coreBlock = error "todo"

--Flushes the 
branch :: Branch -> CoreM ()
branch b = error "todo"

setCurrentFun :: (FunVar,Pattern) -> CoreM ()
setCurrentFun fvp = modify (\s->s{csCurrentFun=fvp})

--Allocates a new function Name, as distinct from a FunVar (which contains
--type info).
newFunName :: CoreM Name
newFunName = newFunName' ""
--Adds an explanatory string
newFunName' :: String -> CoreM Name
newFunName' expl = do
  fv <- ask
  s <- get
  let n = csAllocCtr s
  put s{csAllocCtr = n + 1}
  let FPoly f ts _ = fv
  return $ concat [f,show ts,show n,expl]

--TODO do something prettier
mangleFunVar :: FunVar -> String
mangleFunVar (FPoly f ts _) = f ++ show ts

--scope (including $ret and $stk but not env) = vs => lhs = (v1*v2*...vN,env)
--Type: forall stk . lhs -> End
--The type is put in the FunVar.
scope2LHS :: Scope -> (Pattern,T)
scope2LHS scope = (P $ tupleV [foldr1 Pair $ map Var scope],
                   TyForall "stk" $ tupleT [foldr1 T.Pair $ map typeOfVar scope,
                                            envT])

{-

Approach:
val := Op opE => append (val,op) to ops
v := Call fv val =>
ret <- mkCont retfun scope
branch (Jump fv ((val,ret),env))
retfun: scope = v:scope
--What about val1 := Call fv val2?
Ifte v th el =>
 

Two approaches to cont passing: generate names first and feed them to cont,
or codegen back to front.
Break, continue and return don't have a cont, in which case you can avoid
generating it and just drop the rest of the block. That's simpler than my old
approach of passing a Maybe cont.
Ah, but in ifte you need to pass in a next... so perhaps the tried-and-true
approach is best.
I short-circuited during CFG generation, but it might be simpler to do that
in an inlining pass.

Opts:
if(v) {return f()} el => if (v) f el
{return f()} => (simplified)
call ($ret,env):
 let rc = mkCont ret $ret
 jump f (rc,env)
ret (((),$ret),env):
 jump $ret ((),env)
The if:
if v call el ($ret,env)
A BB is bypassable if 1) it contains no ops, 2) the jump's arg is the same
as the BB's arg. IOW,
f x:
 let {} in jump g x
is bypassable. Bypassable is stronger than inlinable, since if f ~ g then
f can be replaced in jumpis.
Recall, tail call optimization is eta reduction:
if rc ~ $ret you can rewrite f(rc,env) to f($ret,env)
call (the fun above) can then have its unused mkCont op pruned, at which
point it becomes bypassable.
Nested TCO (return f(g(h(x))) => jump h ((x,mkCont g (mkCont f ())),env) =>
jump h (x,g,f) on the stack.
mkCont: Cont (Pair a b) -> b -> Cont a
mkCont f () ~ f --can be applied immediately
Note for writeup: it's the only thing that looks like partial application, but
since mkCont f x is implemented by simply leaving f,x on the stack it's only
compilable if it's the last of the non-zero args.

return f(g(x)) => --simplified, env removed
c1 (x,$ret):
 let rc = mkCont c2 $ret
 jump g (x,rc)
c2 (v,$ret):
 let rc = mkCont c3 $ret
 jump f (v,rc)
c3 (v,$ret):
 jump $ret v
--c3 involves a swap... but calling mkCont undoes it.
mkCont f x = (\v -> f (v,x))
Inlining rc: jump f (v,\v -> c3 (v,$ret))
Inlining c3: jump f (v,\v -> $ret v) => f(v,$ret) by eta reduction
Any function which doesn't touch its last n arguments (f,rest) until it
eventually calls f (retv,rest) can take a mkCont instead for greater
polymorphism.
f : a -> b => coerceFun f : (a,c) -> (b,c)
Core coercion (which requires representational equality) on argument and
result is also a noop at runtime.
General rule: f (scope..ret) where ret ~ \v -> f (v,rest) =>
--f (scope .. mkCont f rest)

Something I absolutely need to do for inlining to work: identify static
function values and delay their push until use (reordering the ops in f x).
s1:
 let fv = f
 in jump s2 fv
s2 fv: jump fv
That works when s1 statically calls s2, passing it f.
That can be generalized to delaying the push of static values when they'll
eventually be ToS, but if there are many user BBs and the SV is large...
Focus on applying it to functions; other constants lack inlining synergy and
may benefit from sharing.
That can be split up: if a static call of f is detected, use a local v instead
of the passed one (duplicating the op). Then if the passed v is unused, elide
it.

I need to add Core function push to Core primops.
if (v) f f args => jump f args
if(v){}el; cont => if(v) cont el; cont

while {} v {}; cont => if v diverge cont
Gas usage isn't part of the spec (otherwise opts would be impossible), so
diverge can be revertValue()
Expose revert off len as a Core construct (synonymous with revert emptyBS)?
Note for terminating branches the state of the stack above (off,len) is
irrelevant, so you can elide stack cleanup (modulo the stack limit).
Possible FW: stack conservatism annots; for now recommend against getting
near the stack limit.
Explicitly pass an extra arg to revert representing unused values?

-}
