{-# LANGUAGE PatternSynonyms, LambdaCase #-}
module Core.Convert where

import AST.DTs (T(..),Name(..),tupleT,Region(Co), pattern UInt)
import qualified AST.DTs as T (pattern Pair)
import Structured.DTs
import Core.RestrictedCore
import Core.PrimTypes (pattern W)
import Const.Const (Serialized(..)) --I need to push function labels...
--TODO encapsulate Serialized, exposing its structure is asking for trouble.

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
  bb_jtmaps <- mapM (\(fv,(p,body)) -> coreF fv p body) defs
  let bbmaps = map fst bb_jtmaps
      jtmaps = map snd bb_jtmaps
  return Core {coreDefuns = M.unions bbmaps
                --TODO union with Core prims: stop, revert, evm_return
               --coreGlobals = sglobals smod,
              ,coreStatic = M.mapMaybe (\case (_,_,Just ser) ->
                                                Just ser
                                              _ -> Nothing) $ sglobals smod
              ,coreJTs = M.unions jtmaps
              }

--No need for break/continue outside loop, it's caught in Structured.
data CoreError = TriedToExitLoopOutsideLoop String
  deriving (Eq,Ord,Read,Show)
{-
State:
loops: [(fcont,scope),(fbreak,scope)]
ops accumulated so far
current Core function being accumulated
-}
type Cont = (FunVar,Scope)
data CoreS = CoreS {
  csAllocCtr :: Int, --for allocating new function names
  --[(break,continue)]
  csLoopStack :: [(Cont,Cont)],
  --csCurrentFun :: (FunVar,BranchValue),
  --csOps :: [(Value,OpE)], --accumulated ops in reverse order
  --The BB map; on a branch the current fun and its ops are flushed to the
  --map.
  csDefuns :: Map FunVar (BranchValue,FunRHS),
  --Convention: all JTs are named $jt<n>
  csJTs :: Map Name [FunVar]
  }
  deriving (Eq,Ord,Read,Show)
--The monad for accumulating the CFG of a single Structured function.
type CoreM = ReaderT FunVar --parent fun; is source module needed?
             (StateT CoreS (Except CoreError))

--Converts a single Structured function to a map of BBs
--It's safe for it to just have $ret in its scope.
--It's fine to reset the alloc counter for each coreF; each anon BB's name will
--also be pased on the parent function.
--Example LHS for f x := x, f@[Bool]:
--f[Bool] (
-- $arg.1:W# (Bool) (1) *
-- $ret:Cont# (SPair# (W# (Bool) (1)) (stk))
--                   (SPair# (MemSlice#)
--                   (SPair# (CalldataState#)
--                   (SUnit#))) *
-- $stk:stk,
-- $mem:MemSlice# * $cd:CalldataState# * ()) := ...
--The use of SPair# in the stack arg of Cont# is a bug, TODO fix.
--Nevertheless, I can extract the scope I need from the BranchValue.
coreF :: FunVar -> BranchValue -> [Stmt] ->
  --TODO return csJTs as well.
  Either CoreError (Map FunVar (BranchValue,FunRHS), --Basic blocks
                    Map Name [FunVar]                --Jump tables
                   )
coreF fv bv@(scope,_,_) body =
  fmap (\s -> (csDefuns s, csJTs s)) $ runExcept $ flip execStateT initSt $
  flip runReaderT fv $ do
  --The Structured fun starts with $arg.1..n,$ret on the stack, not the argument
  --locals (which are extracted from arg via pattern-matching).
  fun <- coreBlock scope (error "The block always returns!") body
  --fv just jumps to fun:
  rhs <- normal [] fun
  modify (\cs->cs{csDefuns = M.insert fv (bv,rhs) $
                             csDefuns cs})
  where initSt = CoreS {
          csAllocCtr = 1,
          csLoopStack = [],
          --csCurrentFun = (fv,p),
          --csOps = [],
          csDefuns = M.empty,
          csJTs = M.empty
          }

--Given its continuation, compiles a block of stmts to a function.
coreBlock :: Scope -> --lhs = (scope,Just stk,envV)
             Cont -> --next cont
             [Stmt] -> --remaining stmts
             CoreM Cont
coreBlock lhs cont stmts = do
  f <- newFunName
  --There should be no need to handle comments in coreBlock' or '':
  rhs <- coreBlock' cont $ filter (\case Comment _ -> False
                                         _ -> True) stmts
  modify (\cs->cs{csDefuns = M.insert f (scope2BV lhs,rhs) $
                             csDefuns cs})
  return (f,lhs)
  
coreBlock' :: Cont -> [Stmt] -> CoreM FunRHS
coreBlock' cont = go
  where go = \case
          --Simply continue to the cont:
          --let xf = push f in jump xf(scope)
          [] -> normal [] cont
          --A series of ops followed by zero or more other stmts:
          --If there are no ops, the normal will be inlined away.
          stmts -> do
            let (ops,rest) = collectOps stmts
            --rest should provide the scope info here
            next <- coreBlock'' cont rest
            normal ops next
--Compiling a [Stmt] starting with a Stmt that provides its own scope info,
--or [] (in which case the cont provides scope info)
coreBlock'' :: Cont -> [Stmt] -> CoreM Cont
coreBlock'' cont stmts =
  case stmts of
    [] -> return cont
    stmt:stmts ->
      case stmt of
        --f(args) in C becomes let ret = push next in jump f, args, ret, scope
        --next expects lhs++scope 
        Call scope lhs f args -> expects scope $ do
          next <- coreBlock (lhs ++ scope) cont stmts
          --The body has only a single op: pushing next
          (ret,o) <- opPushF next
          return ([o], jump f $ args ++ ret : scope)
        --We assemble the control flow graph backward:
        --cond -> decision -> (th | el) -> next
        --decision (condvar:scope) =
        -- let xthen = thcont
        -- in jumpi (xthen,condvar,scope) else
        --  normal [] elcont
        --If ifte always continues to the same scope, I need to account for
        --that in &&, ||.
        Ifte scope cond condvar th el -> expects scope $ do
          next <- coreBlock scope cont stmts
          thcont <- coreBlock scope next th
          --Should usually be inlined into the fallthrough FunRHS in the jumpi.
          elcont <- coreBlock scope next el
          --The then function pointer must be bound to a name in the decision
          --basic block:
          (xthen,othen) <- opPushF thcont
          decision <- expects (condvar:scope) $ do
            jump2el <- normal [] elcont
            return ([othen],
                    Jumpi jump2el $
                    scope2BV $ xthen : condvar : scope)
          condcont <- coreBlock scope decision cond
          normal [] condcont
        --cond:
        -- ...cond
        --jumpi body
        --jump end
        --body:
        -- ...body
        --jump cond
        --end:
        --The many extraneous jumps should be optimized away; if the expected
        --iteration count is high then loop start should jump to cond and
        --body should fall through to it.
        --Note I need to push to the loop stack as well.
        While scope cond condvar body -> do
          --Need to alloc a cont name without binding it to tie the knot:
          continue <- do fnm <- newFunName' "whileStart"
                         return (fnm,scope)
          break <- coreBlock scope cont stmts
        --body needs (break,continue) pushed 
          bodycont <- withLoop (break,continue) $
                      coreBlock scope continue body
          decision <- expects (condvar:scope) $ do
            (xbody,obody) <- opPushF bodycont
            jump2brk <- normal [] break
            return ([obody],
                    Jumpi jump2brk $ scope2BV $ xbody : condvar : scope)
          condcont <- coreBlock scope decision cond
          --continues' rhs; it just jumps to condcont:
          rhs <- normal [] condcont
          modify (\cs->cs{csDefuns = M.insert (fst continue)
                           (scope2BV scope,rhs) $
                           csDefuns cs})
          return continue
        Break scope -> do
          (break,_) <- headLoopStack "break"
          expects scope $ normal [] break
        Continue scope -> do
          (_,continue) <- headLoopStack "continue"
          expects scope $ normal [] continue
        --Assuming $ret is already on the stack:
        Structured.DTs.Return scope vs ->
          expects scope $ return ([], Jump $ scope2BV vs)
        --If n16:
        -- tbl <- push conts as one word in reverse order
        -- jump ((tbl >> tag) & 0xffff) (vs ++ scope)
        --else:
        -- jt <- alloc new code JT, push its address
        -- jump (jt + tag) (vs ++ scope)
        CaseBranch scope n16 vs tag jt -> expects (tag:(vs++scope)) $ do
          next <- coreBlock scope cont stmts
          fs <- map fst <$> mapM (coreBlock (vs++scope) next) jt
          if n16
            then do
            --jump ((tbl >> tag) & 0xffff) (vs ++ scope)
            --TODO make an op emitter monad?
            (jt,op_push_jt) <- pushJT fs
            (shifted,op_shift) <- emitOp (Op "shr") [tag,jt]
            (oxffff,op_0xffff) <- emitOp (Push Serialized {
                                             serLength = 2,
                                             serSizeof = 2,
                                             serContent = [Left [255,255]]
                                             }) []
            (masked,op_mask) <- emitOp (Op "and") [oxffff,shifted]
            return ([op_push_jt,
                     op_shift,
                     op_0xffff,
                     op_mask],
                    jump masked $ vs ++ scope
                   )
            else do
            (jt,op_push_jt) <- allocJT fs
            (sum,op_add) <- emitOp (Op "add") [tag,jt]
            return ([op_push_jt,
                     op_add],
                     jump sum $ vs ++ scope
                   )
        other -> error $ "Compiler error in coreBlock'': " ++ show other

--An ugly solution for emitting code during Core compilation.
--That's necessary because Structured has no concept of case JTs or function
--return addresses.
--TODO make an op emitter monad, or at least reuse in alloc/pushJT and
--opPushF.
emitOp :: PrimOp -> [Var] -> CoreM (Var,(Value,OpE))
emitOp primop vs = do
  v <- newVar $ W (UInt 32) 1
  return $ (,) v $ (,) ([v],[]) $ (primop, (vs,[]))

--Given a list of functions to jump to, allocates a new JT and returns the
--var v it's to be bound to, and the op v = push $jt<n>.
--Used in compiling caseBranch when TagScheme /= N16.
--Code copied from opPushF.
allocJT :: [FunVar] -> CoreM (Var,(Value,OpE))
allocJT fs = do
  n <- alloc
  let jtnm = "$jt"++show n
  modify (\s->s{csJTs = M.insert jtnm fs $ csJTs s})
  let ser = Serialized {serLength = 2,
                        serSizeof = 2,
                        serContent = [Right (0,2,jtnm)]
                       }
  --Giving it a placeholder type for now
  v <- newVar $ W (TyVar "?") 1
  return $ (,) v $ (,) ([v],[]) $ (Push ser, ([],[]))
--Given a list of functions to jump to, handles pushing the JT containing
--those functions as a single word.
--Returns the var v the word is to be bound to and the
--op v = push {fN,f<N-1>,...,f0}.
--Used in compiling caseBranch when TagScheme = N16
--Code copied from opPushF; TODO cleanup
pushJT :: [FunVar] -> CoreM (Var,(Value,OpE))
pushJT fs = do
  let lenn = fromIntegral $ length fs
  if length fs > 16
    then error $ "Compiler error: N16 JT doesn't fit in a word! "
         ++ "\nJT: " ++ show fs
    else return ()
  let ser = Serialized {serLength = 2*lenn,
                        serSizeof = 2*lenn,
                        serContent = [Right (0,2,f) | f <- fs]
                       }
  --Giving it a placeholder type for now
  v <- newVar $ W (TyVar "?") 1
  return $ (,) v $ (,) ([v],[]) $ (Push ser, ([],[]))
--Pushes and then pops break and continue
--Reader would be appropriate here since this is the only way we modify
--the loop stack...
withLoop :: (Cont,Cont) -> CoreM a -> CoreM a
withLoop bc m = do
  ls <- gets csLoopStack
  modify (\cs->cs{csLoopStack=bc:ls})
  a <- m
  modify (\cs->cs{csLoopStack=ls})
  return a
--Gets the top (break,continue) if there is one; errors otherwise
headLoopStack :: String -> CoreM (Cont,Cont)
headLoopStack str = do
  ls <- gets csLoopStack
  case ls of
    [] -> throwError $ TriedToExitLoopOutsideLoop str

--Binds a new function name f: f lhs = rhs and returns the cont.
--Logic copied from coreBlock; TODO deduplicate.
expects :: Scope -> CoreM FunRHS -> CoreM Cont
expects lhs mrhs = do
  f <- newFunName
  rhs <- mrhs
  modify (\cs->cs{csDefuns = M.insert f (scope2BV lhs,rhs) $
                             csDefuns cs})
  return (f,lhs)

--This corresponds to pushLabel2 in Fused.Monad; TODO share code
opPushF :: Cont -> CoreM (Var,(Value,OpE))
opPushF (f,scope) = do
  --From serLabel2 with the ts parameter baked in
  let ser = Serialized {serLength = 2,
                        serSizeof = 2,
                        serContent = [Right (0,2,f)]
                       }
  --Giving it a placeholder type for now
  v <- newVar $ W (TyVar "?") 1
  return $ (,) v $ (,) ([v],[]) $ (Push ser, ([],[]))

jump :: Var -> Scope -> Branch
jump fvar scope = Jump $ scope2BV $ fvar:scope

--The normal Core body: perform some straight-line ops, then perform a static
--jump.
--let ops; xf = push f in jump xf(scope)
--TODO give a better name
normal :: [(Value,OpE)] -> Cont -> CoreM FunRHS
normal ops cont@(_,scope) = do
  --To give the var the right type, you need to know its type.
  --However, that's implicit in scope (since scope also contains $ret)
  (xf,o) <- opPushF cont
  return $ (ops ++ [o], jump xf scope)

--Duplicated from Fused.Monad; TODO share interface
newVar :: T -> CoreM Var
newVar t = do
  n <- alloc
  return $ Mono ("$coreAnon"++show n) t
--I have so many counters... TODO make a single class for them
alloc :: CoreM Int
alloc = do
  cs <- get
  let n = csAllocCtr cs
  put cs{csAllocCtr = n+1}
  return n
    
--Collect the prefix of straight-line ops
collectOps :: [Stmt] -> ([(Value,OpE)],[Stmt])
collectOps = go []
  where go rops = \case
          val := opE : rest -> go ((val,opE):rops) rest
          rest -> (reverse rops, rest)

--Refining the CoreM monad: it consumes stmts, emits Core ops and ultimately
--returns a Branch.
--coreBranch must be monadic because it must allocate new vars...

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
  return $ concat [fv,show n,expl]

--scope (including $ret and $stk but not env) = vs => lhs = (v1*v2*...vN,env)
--Type: forall stk . lhs -> End
--The type is put in the FunVar.
scope2BV :: Scope -> BranchValue
scope2BV scope = (scope,Just $ Mono "$stk" (TyVar "stk"), envV) {-
  (P $ tupleV [foldr1 Pair $ map Var scope],
                   TyForall "stk" $ tupleT [foldr1 T.Pair $ map typeOfVar scope,
                                            envT])
-}
--We don't do any typechecking yet, so this'll do for now.
scope2Type :: Scope -> T
scope2Type _ = TyVar "TODO" 
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
