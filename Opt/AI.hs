module Opt.AI where

import Opt.Concurrent
import Opt.AbVar
import Opt.Semilattice
import Core.RestrictedCore
import Core.SSA (OptCore,OptFunRHS)

import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.Except
import Control.Monad

--The module that defines the EVMC program abstract state and its recursive
--equation.
--Because CB treats Chans as the unit of incremental computation and
--separates them from the monad for constructing circuits, the state and
--its recursive equation can be given a straightforward, readable definition.

--The module state in the solver context.
--I could param by wrapper (Chan s when solving, Id later), but let's not get
--too fancy.

--The f param is Chan s while the mod state is mutable, then Id when it's
--pure.
newtype Id a = Id a
  deriving (Eq,Ord,Read,Show)
type FrozenModState = ModState_ Id
type ModState s = ModState_ (Chan s)
data ModState_ f = MS {
  funInfo :: Map FunVar (FunInfo_ f)
                     }

type FunInfo s = FunInfo_ (Chan s)
data FunInfo_ f = FI {
  fiReachable :: f Bool,
  --We ignore stk for now. mstk will retain its value from the original Core,
  --meaning revert and RETURN won't be able to drop the stack if inlined into
  --a BB which has non-Nothing stack.
  --TODO: non-returning funs should also be able to drop the old stack.
  --The full complement of state vars is always passed.
  fiLHS :: ([AVar_ f],[AVar_ f]),
  --Tells me which vars (lhs and internal) are small constants I can replace
  --with pushes.
  --Combined with the op map from OptCore, it also lets me apply symbolic
  --simplification such as x + 0 => x.
  fiVars :: Map Var (AVar_ f),
  --Tells me which ops are live (an op is live iff any of its lhs vars are
  --live).
  --Ops are identified by their LHS.
  fiOpsLive :: Map Value (f Bool),
  fiPassed :: Maybe ([AVar_ f],[AVar_ f]), --Nothing for exits
  --Need to M.map over funInfo to get the succs map : f => set f.
  succs :: f (Set FunVar),
  preds :: f (Set FunVar)
                    }
--TODO pick more suitable names for AVar, AbVar.
type AVar s = AVar_ (Chan s)
data AVar_ f = AVar {
  avLive :: f Bool,
  avVal :: f AbVar
  }
type AValue s = ([AVar s],[AVar s])
--Problem: bad op names or arities may raise an error. Will that interfere
--with mfix? Whether AI errors is solely dependent on the Core input, so
--it shouldn't be a problem.
--The part of the AI that's run synchronously just sets up the circuit.
--ExceptT inherits MonadFix, so mfix can be run directly in it.
--Computing the opMap circuits immediately (and reporting any errors then)
--would let me run the recursive equation in AI.

--type AIM s a = AIM {unAIM :: ExceptT AIError (AI s) a}
--  deriving (Functor,Applicative,Monad,Concurrent)
data AIError = BadMnemonic String
             | BadArity String (Int,Int) (Int,Int)
             | OutOfScope Var
             | UndefinedLabel String --push error
             --Assumption: no pushes are >32B; that should've already been
             --filtered out.
  deriving (Eq,Ord,Read,Show)

--The mfix problem is solved; next step: define the initial state.
aiModule :: AIC m => OptCore -> ExceptT AIError m FrozenModState
aiModule = error "todo"

initialModState :: AIC m => OptCore -> m (ModState (S m))
initialModState core = do
  fi <- forM (coreDefuns core) initialFunInfo
  return MS{funInfo = fi}

initialFunInfo :: AIC m => (BranchValue,OptFunRHS) -> m (FunInfo (S m))
initialFunInfo (lhs,(ops,branch)) = do
  reachable <- newChan False
  alhs <- initialLHS lhs
  return FI {
    fiReachable = reachable,
    fiLHS = alhs
    }
--Alloc new AVars for ws, ss. They are bottom and not live by default.
initialLHS :: AIC m => BranchValue -> m (AValue (S m))
initialLHS (ws,_,ss) =
  (,) <$> mapM new ws <*> mapM new ss
  where new _ = AVar <$> newChan False <*> newChan bottom

--Backlinking the entire module is overkill and verbose, but simple.
--Assumes ms1 and ms2 have the same shape.
unsafeWireModState :: AIC m => ModState (S m) -> ModState (S m) -> m ()
unsafeWireModState ms1 ms2 =
  zipWithM_ unsafeWireFunInfo
  (M.elems $ funInfo ms1) (M.elems $ funInfo ms2)
unsafeWireFunInfo :: AIC m => FunInfo (S m) -> FunInfo (S m) -> m ()
unsafeWireFunInfo fi1 fi2 = error "todo"

--reachable[f] = any reachable (preds f)
--Add Reader (ModState s)?
eqReachable :: AIC m => ModState (S m) -> FunInfo (S m) -> m (Chan (S m) Bool)
eqReachable ms fi =
  let fs = funInfo ms
  in setAny (\g ->
               case M.lookup g fs of
                 Nothing -> error "!?"
                 Just gi -> fiReachable gi)
     (preds fi)
--Jumpi else branches are now divided into separate basic blocks, so they're
--no longer nested and can all be accessed from coreDefuns.
--Each SLS has its own LHS and liveness status for vars... a var that's live
--in the jumpi may become dead in the else branch.
--The static else branch is now represented as a FunVar rather than a nested
--FunRHS...
--That introduces the possibility of an else branch having multiple
--callers - only one of which may fall through. The rest must be implemented
--as jumps, and if there are several then the branch must have a jumpdest.
--That creates a reason to copy functions, and therefore to re-run AI to get
--more specialization.

--Shallow copy: create a new f' with def identical to f; then any use of
--f can be replaced with f'.
--Deep copy: do the same for the SCC of f (including JTs), but replace any
--mention of the originals with the new ones in the copy.
--Ah, JTs need to be part of the CFG... so they need to have their own
--preds, succs, lhs and end stack.
--If I added jt+k to the abstract state and established bounds on k, I could
--partially GC it - though if a prefix of length L is dropped, the rest would
--need to be at an offset >= L unless the DT tags are changed. FW, for now
--assume it can jump to any JT elem.

--Tracking call and ret means I'm stuck with Structured-level information in
--the Core. The upside is I can share f.ret, needing only to propagate at
--least the ret update through f's BBs on each new call.

--If an else branch takes multiple copies of the same var, you could in theory
--choose which one is live to fit other jumpi dests.

{-
Characterizing BBs:
lhs[f] = known for $trueMain and $stop,
 otherwise lub of passed of all preds modulo calls and returns
passed[f] =
 case branch f of
  jumpi cond,g,rest -> rest
  jump g,rest ->
   case mode jump of
    return -> 
 No entry for exits, they should have succs = {}
vars[f] : v => abvar
The op map determines relations between lhs and internal vars;
bad ops should throw an error.
dests({jt}) = {all fs in jt}

On TCO: a call is of the form callFrame,[partialCallFrame] where ret,scope
is a partial call frame.
If return was treated as a special case of call, fusing call and return
wouldn't require changing the jump type.

$trueMain starts with no stack param, then main has one... how to represent
stk? Nothing ~ the empty stack.
(ws,mstk,...) ~ w1*w2*...toStkVar mstk
The ret cont receives retval...stk, it just unpacks stk more than the callee
(which is polymorphic in stk) does.
For now the stack doesn't need an abstract state except liveness.
To implement the prettier model I'd need polymorphism support in Core +
explicit repr of functions as Conts with no return value.
jump : (Cont stk s * stk, s) -> End

jump f,args,ret,rest => f called with args,ret; ret called with
retval f ++ rest (with excess suffix dropped). Fail on multiple arities,
treat badfun as arity = |retval++rest|.

-}

--On lifting exprs out of loops: vars have a last common ancestor which
--forms a lattice based on the SCC tree of the CFG; later nodes are greater
--than earlier ones.
--Per C function or global?
