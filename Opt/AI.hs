{-# LANGUAGE RankNTypes, LambdaCase, FlexibleContexts #-}
--MonadError AIError requires flexible contexts
module Opt.AI where

import Opt.Concurrent
import Opt.AbVar
import Opt.Semilattice
--import Opt.ModState
import Core.RestrictedCore
import Core.SSA (OptCore,OptFunRHS,OpMap)

import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.Except
import Control.Monad
import Control.Arrow ((***))

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
--Core has defuns, jts, and codeGs.
--Unmentioned codeGs can be pruned after AI by scanning all vars.
--Unmentioned functions can be pruned; mentioned but unreachable functions
--can be given the value 0x01 (ensuring no labels are falsy, which simplifies
--AI).
--JTs have their own reachability status, so succs and preds are not
--function-specific.
--A JT's lhs is the lub of the passed of its preds; its passed is the same,
--and its succs is the list of its funs. (TODO refine succs using dest of its
--preds.)
--It therefore makes sense to store functions and JTs in the same map, since
--they're both executable.
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
  --Both functions and JTs are part of the control and dataflow graph, but
  --only functions have ops.
  fiBodyInfo :: BodyInfo_ f,
  --The f Bool indicates whether the passed var is used by any successor
  fiPassed :: Maybe ([(f Bool, AVar_ f)],
                     [(f Bool, AVar_ f)]
                    ), --Nothing for exits
  --Need to M.map over funInfo to get the succs map : f => set f.
  succs :: f (Set FunVar),
  preds :: f (Set FunVar)
                    }
type BodyInfo s = BodyInfo_ (Chan s)
data BodyInfo_ f = IsJT --no ops
                 | IsFun {
                     --Tells me which vars (lhs and internal) are small
                     --constants I can replace
                     --with pushes.
                     --Combined with the op map from OptCore,
                     --it also lets me apply symbolic
                     --simplification such as x + 0 => x.
                     fiVars :: Map Var (AVar_ f),
                     --Tells me which ops are live (an op is live iff any of
                     --its lhs vars are live).
                     --Ops are identified by their LHS.
                     fiOpsLive :: Map Value (f Bool)
                     }
--TODO pick more suitable names for AVar, AbVar.
type AVar s = AVar_ (Chan s)
data AVar_ f = AVar {
  avLive :: f Bool,
  avVal :: f AbVar
  }
--Passed also requires info on whether the given position is demanded by
--any successor.
type Passed s = ([(Chan s Bool, AVar s)],[(Chan s Bool, AVar s)])
type AValue s = ([AVar s],[AVar s])
--Freezable doesn't work for DT (Chan s | Id)
--Barbies (the package) doesn't seem to fit the datatypes because their
--structure is too complex... better write manual HTraversable instances.
class HTraversable t where
  htraverse :: Applicative f =>
    (forall a . g a -> f (h a)) -> t g -> f (t h)
instance HTraversable AVar_ where
  htraverse f av = AVar <$> f (avLive av) <*> f (avVal av)
instance HTraversable BodyInfo_ where
  htraverse f = \case
    IsJT -> pure IsJT
    bi -> IsFun <$>
          (htMap $ htraverse f) (fiVars bi) <*>
          (htMap f) (fiOpsLive bi)
instance HTraversable FunInfo_ where
  htraverse f fi = FI <$>
                   f (fiReachable fi) <*>
                   (htPair $ htList $ htraverse f) (fiLHS fi) <*>
                   htraverse f (fiBodyInfo fi) <*>
                   htMaybe (htPassed f) (fiPassed fi) <*>
                   f (succs fi) <*>
                   f (preds fi)
instance HTraversable ModState_ where
  htraverse f ms = MS <$> htMap (htraverse f) (funInfo ms)
--Helpers for defining htraversable
htMaybe :: Applicative f => (a -> f b) -> Maybe a -> f (Maybe b)
htMaybe f = \case
  Nothing -> pure Nothing
  Just x -> Just <$> f x
--TODO make prettier
htPassed :: Applicative f =>
  (forall a . g a -> f (h a)) ->
  ([(g Bool, AVar_ g)], [(g Bool, AVar_ g)]) ->
  f ([(h Bool, AVar_ h)], [(h Bool, AVar_ h)])
htPassed f (bws,bss) = (,) <$> go bws <*> go bss
  where go x = traverse (\(ga,tg) -> (,) <$> f ga <*> htraverse f tg) x
htPair f p = (,) <$> f (fst p) <*> f (snd p)
htList f = traverse f
htMap f = traverse f

freezeModState :: AIC m => ModState (S m) -> m FrozenModState
freezeModState = htraverse ((Id <$>) . readChan)

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
aiModule :: (AIC m, Concurrent m, MonadError AIError m) =>
  OptCore -> m FrozenModState
aiModule core = do
  initial <- initialModState core
  --The meat of the logic: the equation defining module state
  final <- aiEquation core initial
  --Loop it back to itself to make it recursive
  unsafeWireModState final initial 
  scheduler
  freezeModState initial

initialModState :: AIC m =>
  OptCore -> m (ModState (S m))
initialModState core = do
  fim <- mapM initialFunInfo $
        M.union (M.map Left $ coreDefuns core) $
        M.map Right $ coreJTs core
  --Set reachable trueMain to True
  true <- newChan True
  return MS{funInfo = M.adjust (\fi -> fi{fiReachable=true}) "$trueMain" fim}

--Applies to both Core functions and JTs
initialFunInfo :: AIC m =>
  Either (BranchValue,OptFunRHS) ((Int,Int),[FunVar]) ->
  m (FunInfo (S m))
initialFunInfo ei_fun_jt {-(lhs,(ops,branch))-} = do
  reachable <- newChan False
  alhs <- initialLHS ei_fun_jt
  --The vars and ops don't need to be wired together here, so init is simple
  --All vars in the opmap are results of ops, so none are shared with the lhs.
  --However, it's helpful to add the lhs vars in order to simplify passed
  --computation and the circuit.
  --Opt when wiring: since the lhs vars are in vars, you don't need to wire
  --the lhses. Ditto for passed.
  bi <- case ei_fun_jt of
          Left (lhs,(ops,branch)) -> do
            (vars,opsLive) <- initialVarsOps lhs alhs ops
            return IsFun {fiVars = vars,
                          fiOpsLive = opsLive
                         }
          Right _ -> return IsJT
  --Opt: the vars in passed can be looked up 
  passed <- case ei_fun_jt of
             Left (lhs,(_,branch)) ->
               initialPassed (fiVars bi) branch
             Right _ -> Just <$> addBools alhs
  ss <- case ei_fun_jt of
          Left _ -> newChan S.empty
          Right (_,fs) -> newChan $ S.fromList fs
  ps <- newChan S.empty
  return FI {
    fiReachable = reachable,
    fiLHS = alhs,
    fiBodyInfo = bi,
    fiPassed = passed,
    succs = ss,
    preds = ps
    }
--JTs have a lhs, so Core must contain a record of its stack and state arity.
--Obscure opt: BBs which are <= 4 bytes could be inlined directly into the JT,
--e.g. stop or revert(0,1). Then every JT entry could be an inlined exit,
--at which point the JT shouldn't have a pass. Not worth implementing, direct
--jump JTs are a better use of effort (jump eliminated, no BB size constraint
--but complex placement constraint).
--TODO implement N5 tag scheme, which saves 8 gas per case for DTs with
--between 3 and 52 constructors (in practice all DTs with >2 constructors except
--isets with many instructions).
    
--Alloc new AVars for ws, ss. They are bottom and not live by default.
initialLHS :: AIC m =>
  Either (BranchValue,OptFunRHS) ((Int,Int),[FunVar]) ->
  m (AValue (S m))
initialLHS ei_fun_ss =
  let (lenw,lens) =
        case ei_fun_ss of
          Left ((ws,_,ss),_) -> (length ws, length ss)
          Right (arity,_) -> arity
  in (,) <$> replicateM lenw initialAVar <*> replicateM lens initialAVar  
--Inefficiency: the OpMap should really contain a Var => Value map
--and a Value => OpE map, since ops are keyed by Value.
--Now I need to reconstruct those maps when computing opsLive.
--Algo:
--vars = lhsmap
--opsLive = {}
--for each (lhs,opE) in ops:
-- opsLive[lhs] = newChan False
-- for each var in lhs:
--  vars[var] = initialAVar
--But since I need to reconstruct the lhs map:
--for each (var,(lhs,opE)) in ops:
-- vars[var] = initialAVar
-- if lhs not in opsLive:
--  opsLive[lhs] = newChan False
initialVarsOps :: AIC m =>
  BranchValue -> AValue (S m) -> OpMap ->
  m (Map Var (AVar (S m)), Map Value (Chan (S m) Bool))
initialVarsOps (ws,_,ss) (wchs,schs) ops =
  --Precondition: no repeated vars
  let lhsmap = M.fromList $ zip (ws ++ ss) (wchs ++ schs)
  in go lhsmap M.empty $ M.toList ops
  where
    go vars opsLive = \case
      [] -> return (vars,opsLive)
      (v,(lhs,_opE)):ops -> do
        av <- initialAVar
        opsLive' <- if M.member lhs opsLive
                    then return opsLive
                    else do
          bch <- newChan False
          return $ M.insert lhs bch opsLive
        go (M.insert v av vars) opsLive' ops
--Precondition: all vars in the branch are in scope (defined by vars).
--TODO throw an exception if that's not true?
--Note the passed on calls may exceed call arity and vice versa for returns.
--Must now be monadic because it may allocate new Bool chans.
initialPassed :: AIC m =>
  Map Var (AVar (S m)) -> Branch -> m (Maybe (Passed (S m)))
initialPassed vars = \case
  Jump _mode bv -> Just <$> addBools (dropJump $ bv2aval bv)
  Jumpi fv bv -> Just <$> addBools (dropJumpi $ bv2aval bv)
  _ -> return Nothing
 where bv2aval (ws,_,ss) = (map lookup ws, map lookup ss)
       lookup v = case M.lookup v vars of
                    Nothing -> error "!!? Precondition violated!"
                    Just av -> av
initialAVar :: AIC m => m (AVar (S m))
initialAVar = AVar <$> newChan False <*> newChan bottom

--Drops the first word var (dest) from a value
dropJump p = (drop 1 *** id) p
--Drops the first two word vars (cond,dest) from a value
dropJumpi p = (drop 2 *** id) p
--Pairs each var of a value with a false Boolean chan
addBools :: AIC m =>
  ([a],[b]) -> m ([(Chan (S m) Bool,a)],
                  [(Chan (S m) Bool,b)])
addBools (as,bs) = (,) <$> add as <*> add bs
  where add = mapM (\x -> do
                       bch <- newChan False
                       return (bch,x))

--Backlinking the entire module is overkill and verbose, but simple.
--Assumes ms1 and ms2 have the same shape.
--Or is it...? Liveness flows in the opposite direction from var values, so
--one can't get any savings from making op map evaluation non-recursive.
unsafeWireModState :: AIC m => ModState (S m) -> ModState (S m) -> m ()
unsafeWireModState ms1 ms2 =
  zipWithM_ unsafeWireFunInfo
  (M.elems $ funInfo ms1) (M.elems $ funInfo ms2)
unsafeWireFunInfo :: AIC m => FunInfo (S m) -> FunInfo (S m) -> m ()
unsafeWireFunInfo fi1 fi2 = do
  unsafeWire (fiReachable fi1) (fiReachable fi2)
  --Wiring lhs and passed is redundant, since the AVars occur in fiVars.
  unsafeWireBodyInfo (fiBodyInfo fi1) (fiBodyInfo fi2) fi1 fi2
  unsafeWire (succs fi1) (succs fi2)
  unsafeWire (preds fi1) (preds fi2)
    
--If the node is a function then wiring lhs and passed is redundant, since the
--AVars occur in fiVars. If the node is a JT then lhs and passed are wired
--instead of vars.
unsafeWireBodyInfo :: AIC m =>
  BodyInfo (S m) -> BodyInfo (S m) ->
  FunInfo (S m) -> FunInfo (S m) ->
  m ()
unsafeWireBodyInfo bi1 bi2 fi1 fi2 =
  case (bi1,bi2) of
    (IsJT,IsJT) -> do
      wireVal (fiLHS fi1) (fiLHS fi2)
      let (Just p1, Just p2) = (fiPassed fi1, fiPassed fi2)
      zipWithM_ unsafeWire (passed2bs p1) (passed2bs p2)
      --Redundant, since the vars of passed = the lhs:
      --wireVal (passed2val p1) (passed2val p2)
    (IsFun{},IsFun{}) -> do
      zipWithM_ unsafeWireAV (M.elems $ fiVars bi1) (M.elems $ fiVars bi2)
      --Assumes the maps have the same shape:
      --Using a mapM with key on the first map and looking up keys in the
      --second map would add a log(n) complexity factor.
      zipWithM_ unsafeWire (M.elems $ fiOpsLive bi1) (M.elems $ fiOpsLive bi2)
    _ -> error "Precondition violated: shape mismatch in unsafeWireBodyInfo"
  where wireVal (ws1,ss1) (ws2,ss2) =
          zipWithM_ unsafeWireAV (ws1++ss1) (ws2++ss2)
        passed2bs (bws,bss) = map fst bws ++ map fst bss
        passed2val = map snd *** map snd
unsafeWireAV :: AIC m => AVar (S m) -> AVar (S m) -> m ()
unsafeWireAV av1 av2 = do
  unsafeWire (avLive av1) (avLive av2)
  unsafeWire (avVal av1) (avVal av2)

--Defines the module's abstract state in terms of itself; it's looped back and
--run to a fixpoint.
--Throws an AIError if a malformed Core op is encountered.
aiEquation :: (AIC m, MonadError AIError m) =>
  OptCore -> ModState (S m) -> m (ModState (S m))
aiEquation core ms = do
  let fim = funInfo ms
  --First: define preds in terms of succs
  let succsMap = M.map succs fim
  predsMap <- runCB $ invertGraph succsMap
  --Need to map funInfo with keys to get the key for predsMap
  let f_fis = M.toList fim
  fim' <- M.fromList <$>
          mapM (\(f,fi) -> (,) f <$> fiEquation core ms predsMap (f,fi))
          f_fis
  return MS {funInfo = fim'}

--FunInfo equation:
fiEquation :: (AIC m, MonadError AIError m) =>
              OptCore -> ModState (S m) ->
              Map FunVar (Chan (S m) (Set FunVar))  ->
              (FunVar, FunInfo (S m)) ->
              m (FunInfo (S m))
fiEquation core ms predsMap (f,fi) = do
  reachable <- eqReachable ms fi
  return FI {
    fiReachable = reachable,
    fiLHS = error "todo",
    fiBodyInfo = error "todo",
    fiPassed = error "todo",
    succs = error "todo",
    preds = case M.lookup f predsMap of
              Nothing -> error "!!?"
              Just ps -> ps
    }

--reachable[f] = any reachable (preds f)
--Taking continues into account:
--reachable[f] = any reachable *and not continues* (preds f)
--Add Reader (ModState s)?
eqReachable :: AIC m => ModState (S m) -> FunInfo (S m) -> m (Chan (S m) Bool)
eqReachable ms fi =
  let fs = funInfo ms
  in setAny (\g ->
               case M.lookup g fs of
                 Nothing -> error "!?"
                 Just gi -> fiReachable gi)
     (preds fi)
--Jump modes (call, return, continue, ipc) are still relevant:
--call f,args,ret,scope --continues to ret with scope passed if f may return.
--succs, preds : f => g => mode?
--Q: can f goto g with multiple modes?
--f,args [retconts] sets up a number of dataflow rels.
--Each retcont is of form <f:(A+B)->C,partial:B>:A -> C
--A nested tail call implies multiple call,continue relations.
--Must I add a concept of C functions and may return or is reachable enough?
--Ideally the continue dataflow would only trigger if the callee may return.
--C function f may return iff any returning BB in f is reachable.
--Edges between C functions may only go through roots, so calls to a BB
--within f that may not return is impossible; only root may-return needs to
--be tracked.
--If an RC may not return then the stack below it can be discarded and the
--caller BB may not return.
--Track must exit?
--The invertGraph pattern ~ message-passing for recursive equations.
--No TCO for now. Mode must be recorded in preds and succs; continues edges
--set scope vars but not reachable. Since jump f,args,ret adds ret to the
-- $ret of f, ret will be considered reachable if f may return.
--succs[f] must be {} until f is reachable.
--succs : f => g => branchType
--A jump v,args,w with mode calling (args,rets) has a normal successor for each
--f <- v and a continues(args,rets) successor for each ret <- w.
     
--lhs abvars = elementwise lub of passed of all preds f
--Modification taking continues into account:
--given f lhs = ...
--for each pred g,
-- if branchType is normal then lhs += passed[g] as before
-- else it's continues(args,rets):
--  (drop rets *** id) lhs += (drop (args+1) *** id) passed[g]
--Why args+1? Can't forget the ret param.
--The abvars and liveness per var could be computed in two different passes...
lhsAbVars :: AIC m =>
  ModState (S m) -> --FunInfo (S m) -> --TODO add to Reader context?
  BranchValue -> --Core lhs, tells us which Var the AbVars correspond to
  Chan (S m) (Set FunVar) -> --predecessors
  m ([Chan (S m) AbVar],[Chan (S m) AbVar])
lhsAbVars ms (ws,_,ss) predecessors =
  let (lenw,lens) = (length ws, length ss)
  in runCB $ forAll ((,) <$> replicateM lenw (newInChan bottom)
                     <*> replicateM lens (newInChan bottom)) predecessors
     --For each f, look up (ws,ss) = passed[f] and link them to the inchans
     --Note the length of ws may differ from that expected due to call
     --(passes more) or ret (passes less). That's fine, then we simply don't
     --link the excess vars.
     (\(wins,sins) f ->
        case M.lookup f $ funInfo ms of
          Nothing -> error "!?"
          Just fi ->
            case fiPassed fi of
              Nothing -> error "An exiting BB has a successor!?"
              Just (bs_ws,bs_ss) -> do
                let (ws,ss) = (map (avVal.snd) bs_ws, map (avVal.snd) bs_ss)
                zipWithM_ lubLink ws wins
                zipWithM_ lubLink ss sins
     )
  where
    lubLink :: (JoinSemilattice a, Eq a) =>
               Chan s a -> InChan iv s a -> CB iv s ()
    lubLink from to = do
      subWhenChan (\a -> modInChan (\/ a) to) from
      return ()

-- $trueMain has no preds, so its lhs remains constant.
-- TODO set $trueMain to reachable.
--What should the initial value of the state vars be? {mayBeK}?

--Each var is live iff
--1) any op with rhs containing var is live
--2) any position in passed(branch) which contains var is live
--Minor opt: the set of vars per rhs could be shared for each var's live
--definition.

--For each (lhs,opE) in ops:
-- avs = op rhs
-- rhs live iff any consumers live
-- opsLive[lhs] = any avs live
-- for i in lhs:
--  vars[lhs[i]] = avs[i]
--No need to eval ops in topological order, since op can just read from
--the recursive input.
--Ah: need to record liveness per index in passed; the var at that position
--is live if the position is.
--Note passed doesn't include jumpi cond,dest or jump dest; those vars are
--always live.
--The position is live iff any successor has a live var at the corresponding
--position.
--Note a var in a live position must be live, but not vice versa, since the
--var might be used elsewhere even if the position is ignored.
--lhs position liveness is equal to var liveness, since the lhs contains no
--duplicate vars and the lhs is their source.
--Alternative def that doesn't require a new field: if v is in pos ix of
--passed, include each var at corresponding ix of lhs of callees in consumers.
--Consumers may be ops or branch slots.
--Problem: that means the consumer set grows, so a setFoldr that allocates
--a Set chan would be required. Better to allocate a few Bool chans, isolate
--the propagation and keep the consumer *list* fixed.

--An op (lhs,(primop,rhs)) is live iff any var in its lhs is live.
--That livens every var in the rhs.
--What about y = 0*x? That will liven x in the initial pass, but after
--symbolic simplification it becomes y = 0, eliminating the false dependency.

--Liveness per branch:
--jump dest, jumpi cond,dest always live; rest[i] is live iff args[i] is
--live for any succs.
--For exits, all params are live.

--succs, preds already defined.

-- ****************************TCO********************************************

--A call is of form jump f,args,[retconts] where retconts is terminated by
-- $ret or ipc,scope. A retcont that expects n words is of form f,rest; when
--returned to it becomes f,retval,rest.
--Requirement: f ignores stack below args until it returns to the first word
--of [retconts].
--If f retval,rest = f',retval,rest' then <f,rest> ~ <f',rest'> (with ops
--lifted to the TCO'd caller).
--Nested TCO uses the ~ relation on [retconts].
--Retconts have args and rets arity; [retconts] has a concat operator
--(++) : (a => b) -> (b => c) -> (a => c) and identity [] : a => a.
--Rear partial application reduces args arity of a retcont.

--Simple TCO example: return f x.
--call scope,$ret = jump f,x,[<cont,scope,$ret>]
--cont retval,scope,$ret = $ret,retval
-- <cont,scope,$ret> ~ <$ret>
--return f (g x): here cont,scope,$ret can be replaced with two retconts.

-- ***************************************************************************

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
