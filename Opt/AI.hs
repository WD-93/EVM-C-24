{-# LANGUAGE RankNTypes, LambdaCase, FlexibleContexts,
 StandaloneDeriving, FlexibleInstances, PatternSynonyms #-} --for testing
--MonadError AIError requires flexible contexts
module Opt.AI where

import Opt.Concurrent
import Opt.AbVar
import Opt.Semilattice
import Opt.HTraversable
import Opt.AI.EVM (opBehavior,pushBehavior)
--import Opt.ModState
import Core.RestrictedCore
import Core.PrimTypes hiding (pattern Arg) --for debug print (W)
import AST.DTs (pattern UInt) --for debug print
import Core.SSA (OptCore,OptFunRHS,OpMap)
import Util (unsafePrint')
import Opt.CodeG2Labels (codeG2Labels)

import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Map (Map(..))
import qualified Data.Map as M hiding ((!)) --(!) is a footgun
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad
import Control.Arrow ((***))

debugFlag = True
unsafePrint str = unsafePrint' debugFlag str

--TODO:
--Initial mem, sto, tsto = 0. Loop back sto and tsto from every exit to
-- $trueMain.
--code, calldata, ext, other = bottom{possKs=All}

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
{-
newtype Id a = Id a
  deriving (Eq,Ord,Read,Show)
unId :: Id a -> a
unId (Id a) = a
-}
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
deriving instance Show (ModState_ Id) --for testing
type FrozenFunInfo = FunInfo_ Id
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
  succs :: f (Map FunVar BranchType),
  preds :: f (Map FunVar BranchType),
  --Only relevant to calls: if f has badFunSuccs[g]=(args,rets),
  --then g is passed rets arbitrary words from badfun and scope from f.
  --Badfun is any non-fun, non-jt[ix] value, e.g. coerce 42 :: Word -> Word.
  --It's not added to the CFG when called, but it's assumed it may return.
  --TODO distinguish {jt,mayBeK} from jt+k in AbVar?
  --No, a non-call jump already ignores mayBeK.
  badFunSuccs :: f (Map FunVar (Int,Int)),
  badFunPreds :: f (Map FunVar (Int,Int))
                    }
deriving instance Show (FunInfo_ Id) --for testing
data BranchType = Normal --call, return, ipc: a real direct jump
                --call continues to; establishes dataflow but not reachability
                | Continues (Int,Int)              
  deriving (Eq,Ord,Read,Show)
type FrozenBodyInfo = BodyInfo_ Id
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
deriving instance Show (BodyInfo_ Id) --for testing
--TODO pick more suitable names for AVar, AbVar.
type FrozenAVar = AVar_ Id
type AVar s = AVar_ (Chan s)
data AVar_ f = AVar {
  avLive :: f Bool,
  avVal :: f AbVar
  }
deriving instance Show (AVar_ Id) --for testing
--Passed also requires info on whether the given position is demanded by
--any successor.
type Passed s = ([(Chan s Bool, AVar s)],[(Chan s Bool, AVar s)])
type AValue s = ([AVar s],[AVar s])
--Freezable doesn't work for DT (Chan s | Id)
--Barbies (the package) doesn't seem to fit the datatypes because their
--structure is too complex... better write manual HTraversable instances.
{-
class HTraversable t where
  htraverse :: Applicative f =>
    (forall a . g a -> f (h a)) -> t g -> f (t h)
-}
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
                   f (preds fi) <*>
                   f (badFunSuccs fi) <*>
                   f (badFunPreds fi)
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
             | BadArity ArgOrRet String (Int,Int) (Int,Int)
             | OutOfScope Var
             | UndefinedLabel String --push error
             --Assumption: no pushes are >32B; that should've already been
             --filtered out.
             --Used for debugging
             | GenericAIError String
  deriving (Eq,Ord,Read,Show)
data ArgOrRet = Arg | Ret
  deriving (Eq,Ord,Read,Show)

--Putting it all together:
ai :: OptCore -> Either AIError FrozenModState
ai core = runAI $ runExceptT $ aiModule core

--The mfix problem is solved; next step: define the initial state.
aiModule :: (AIC m, Concurrent m, MonadError AIError m) =>
  OptCore -> m FrozenModState
aiModule core = do
  initial <- initialModState core
  --The meat of the logic: the equation defining module state
  final <- aiEquation core initial
  --Loop it back to itself to make it recursive
  --Bug: the initial values of final are ofc bottom, e.g. reachable is False.
  --If they're written to the values of initial before propagation of
  --values >= bottom from initial, that incorrectly sets the entire circuit
  --to bottom. Rather than naively writing in unsafeWire, the initial
  --must be LUB'd with final.
  unsafeWireModState core final initial 
  scheduler
  freezeModState initial

--TODO set $trueMain's initial state vars:
--memory: 0
--storage: 0
--tstorage: 0
--calldata: All
--returndata: 0
--extstate: All
--other: All
--On the All states: they're considered to contain no functions and are
--treated as arbitrary constants. The 0 states are those solely controlled by
--EVMC. It might seem strange to set storage and tstorage (which might be
--set by an earlier CALL) to be 0 initially, but looping the output of each
--exit to $trueMain ensures the effect of repeated calls is considered.
--TODO set all functions mentioned in codeGs to reachable!
--Refinement: codecopy off g should add only the fs and gs mentioned by g's
--initializer to $memory. Then need a g => set (lt,label) map.
initialModState :: AIC m =>
  OptCore -> m (ModState (S m))
initialModState core = do
  fim <- mapM initialFunInfo $
        M.union (M.map Left $ coreDefuns core) $
        M.map Right $ coreJTs core
  --Set reachable trueMain to True
  true <- newChan True
  --Allocate initial state value chans. Setting $trueMain's fiLHS to new
  --AVars breaks the circuit by eliminating sharing (another way the
  --circuit/modstate abstraction is fragile). Hack: we instead extract the
  --chans and unsafeWire the throwaway initSVs to them.
  initSVs <- initialStateValues
  let Just fi = M.lookup "$trueMain" fim
      ([],svs) = fiLHS fi
  zipWithM_ unsafeWire initSVs $ map avVal svs
  return MS{funInfo = M.insert "$trueMain" fi{fiReachable=true} fim}
--[mem,sto,tsto,cd,rd,ext,other]
--Mem is initially 0
--Sto and tsto likewise
--Calldata is arbitrary; we assume it cannot liven labels
--Ditto for returndata, ext, other: since they come from outside the
--contract where EVMC's abstractions don't hold, we assume we have no control
--over their abstract value. Their abstract value is actually ignored by ops
--that use them, but they still need to be assigned one to fit in the AI
--model.
initialStateValues :: AIC m => m [Chan (S m) AbVar]
initialStateValues =
  mapM newChan [z,z,z,
                arb,
                z, --returndata is initially 0; *CALL sets it 
                arb,arb]
  where z = exactly 0
        arb = bottom{possKs = All}
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
  --The constant successors for JTs need not be computed here, since it
  --must be computed in fiEquation anyway.
  ss <- newChan M.empty
  ps <- newChan M.empty
  bfss <- newChan M.empty
  bfps <- newChan M.empty
  return FI {
    fiReachable = reachable,
    fiLHS = alhs,
    fiBodyInfo = bi,
    fiPassed = passed,
    succs = ss,
    preds = ps,
    badFunSuccs = bfss,
    badFunPreds = bfps
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
--Drops the first two word vars (dest,cond) from a value
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
unsafeWireModState :: AIC m =>
  OptCore -> --for feeding back sto,tsto,ext from stop/return
  ModState (S m) -> ModState (S m) -> m ()
unsafeWireModState core ms1 ms2 = do
  wireMap unsafeWireFunInfo (funInfo ms1) (funInfo ms2)
  --sto, tsto and ext in stop/return must be fed back to $trueMain
  --stop order: sto,tsto,ext
  --return order: mem,sto,tsto,ext
  --truemain order: mem,sto,tsto,cd,rd,ext,other
  --TODO use same lookup logic as in Opt.AI.EVM
  let Just trueMainFi = M.lookup "$trueMain" $ funInfo ms2
      ([],[_mem,sto,tsto,_cd,_rd,ext,_other]) = fiLHS trueMainFi
  --For each reachable BB with stop or EVM return branch, collect its
  --(sto,tsto,ext). Wire each to trueMain.
  --Since FunInfo doesn't record vars passed to an exit, I must recover them
  --using the Core branch and fiVars.fiBodyInfo.
  --For each f in funInfo:
  --Ah, need to add Core as a param.
  let exit2ste =
        M.mapMaybe (\(_lhs,(_obs,branch)) ->
                       --Why not use a list that could be mapped more
                       --succinctly? To make bad lists unrepresentable.
                       --Other could be fed back, but since it has no effect
                       --on op abvars anyway...
                       case branch of
                         Return (_,[_mem,sto,tsto,ext,_other]) ->
                           Just (sto,tsto,ext)
                         Stop (_,[sto,tsto,ext,_other]) ->
                           Just (sto,tsto,ext)
                         _ -> Nothing
                   ) $
        coreDefuns core
      --Get the AbVar chans from the Vars; liveness if ofc not wired.
      exit2abvs =
        M.mapWithKey (\f (x,y,z) ->
                         let Just fi = M.lookup f (funInfo ms1)
                             IsFun {fiVars=v2av} = fiBodyInfo fi
                             (Just abvx, Just abvy, Just abvz) =
                               mapTriplet ((avVal<$>).flip M.lookup v2av)
                               (x,y,z)
                         in (abvx,abvy,abvz))
                 exit2ste
  forM_ exit2abvs (\(stoOut,tstoOut,extOut) -> do
                    unsafeWire stoOut $ avVal sto
                    unsafeWire tstoOut $ avVal tsto
                    unsafeWire extOut $ avVal ext)
    where mapTriplet f (x,y,z) = (f x, f y, f z)
unsafeWireFunInfo :: AIC m => FunInfo (S m) -> FunInfo (S m) -> m ()
unsafeWireFunInfo fi1 fi2 = do
  unsafeWire (fiReachable fi1) (fiReachable fi2)
  --Wiring lhs and passed is redundant, since the AVars occur in fiVars.
  --AHA, not quite! The passed position liveness Bools do not occur in AVars.
  case fiPassed fi1 of
    Just (b_ws1, b_ss1) -> do
      let Just (b_ws2, b_ss2) = fiPassed fi2
      zipWithM_ unsafeWire (map fst b_ws1) $ map fst b_ws2
      zipWithM_ unsafeWire (map fst b_ss1) $ map fst b_ss2
      {-case fiBodyInfo fi1 of
        IsFun fivs fiols ->
          if M.member (Mono "ret!1" (W (UInt 32) 1)) fivs
          then runCB $ do
            unsafePrint $ "Woo " ++ show (M.keys fivs)
            if length b_ws1 /= length b_ws2
              then error $ "Gotcha: " ++ show (length b_ws1, length b_ws2)
              else return ()
            let [finalRet] = map fst b_ws1
                [initialRet] = map fst b_ws2
            subWhenChan (\b -> unsafePrint $
                          "finalRet = " ++ show b) finalRet
            subWhenChan (\b -> unsafePrint $
                               "initialRet = " ++ show b) initialRet
            return ()
          else return ()
        _ -> return ()-}
    Nothing -> return ()
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
      wireMap unsafeWireAV (fiVars bi1) (fiVars bi2)
      --Assumes the maps have the same shape:
      --Using a mapM with key on the first map and looking up keys in the
      --second map would add a log(n) complexity factor.
      wireMap unsafeWire (fiOpsLive bi1) (fiOpsLive bi2)
    _ -> error "Precondition violated: shape mismatch in unsafeWireBodyInfo"
  where wireVal (ws1,ss1) (ws2,ss2) =
          zipWithM_ unsafeWireAV (ws1++ss1) (ws2++ss2)
        passed2bs (bws,bss) = map fst bws ++ map fst bss
        passed2val = map snd *** map snd
--Checking the liveness bug isn't from bad wiring:
wireMap wire m1 m2 =
  let ks1 = M.keys m1
      ks2 = M.keys m2
  in if ks1 /= ks2
     then error $ "Map shape mismatch in wireMap: " ++ show (ks1,ks2)
     else zipWithM_ wire (M.elems m1) (M.elems m2)
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
      badSuccsMap = M.map badFunSuccs fim
  predsMap <- runCB $ invertLabeledGraph succsMap
  badPredsMap <- runCB $ invertLabeledGraph badSuccsMap
  --Create the codeG->mentioned labels map; error immediately if it's
  --malformed.
  c2ls <- case codeG2Labels core of
            Left err -> error $ "Compiler error in codeG2Labels: " ++ show err
            Right c2ls -> return c2ls
  --Need to map funInfo with keys to get the key for predsMap
  let f_fis = M.toList fim
  fim' <- flip runReaderT (core,ms) $
          M.fromList <$>
          mapM (\(f,fi) -> (,) f <$> fiEquation c2ls predsMap badPredsMap
                           (f,fi))
          f_fis
  return MS {funInfo = fim'}

--FunInfo equation:
--Do I really need opsLive? Once Var liveness has been solved I can infer it
--from that. But AVars are consumed by ops; opsLive prevents the AVar from
--being notified every time a var in the lhs becomes live.
--TODO collect storage and tstorage from each STOP and RETURN branch and
--lub it with $trueMain's lhs.
--TODO reuse logic from Opt.AI.EVM for getting the index of state vars
--(I might add more).
--Simplification for debug: broke out the abvar and liveness calculation.
--TODO separate liveness per var and op from the stitching with abvar chans.
fiEquation :: (AIC m, MonadError AIError m,
               MonadReader (OptCore, ModState (S m)) m) =>
              Map FunVar AbVar -> --codeG => labels
              Map FunVar (Chan (S m) (Map FunVar BranchType))  ->
              Map FunVar (Chan (S m) (Map FunVar (Int,Int))) ->
              (FunVar, FunInfo (S m)) ->
              m (FunInfo (S m))
fiEquation c2ls predsMap badPredsMap (f,fi) = do
  (core,ms) <- ask
  reachable <- eqReachable ms fi
  let Just ps = M.lookup f predsMap
      Just bps = M.lookup f badPredsMap
  (lhsavs,bi,mpassed,ss,bss) <-
    case () of
      _ | Just ((wvs,_,svs),(ops,branch)) <- M.lookup f $ coreDefuns core -> do
            (lhs,v2abv,ss,bss) <-
              fiEqAbVarsFun c2ls wvs svs ops branch ms fi ps bps
            --Bug: fiEqLiveFun treated wvs, svs as the vars of passed, but
            --they're actually from the lhs.
            --Adding passed Vars mvps:
            let mvps = branchPassed branch
            --Maybe live of passed
            mlps <- case branchPassed branch of
                      Just (wps,sps) ->
                        Just <$> livePassed (length wps, length sps) ss bss
                      _ -> return Nothing
            let demand = getDemandFromBranch mlps branch
            
            (lhsavs,bi,mpassed) <- fiEqLiveFun wvs svs mvps ops demand
              {-branch-} fi mlps v2abv
            return (lhsavs,bi,mpassed,ss,bss)
        | Just ((wlen,slen),fs) <- M.lookup f $ coreJTs core -> do
            (lhs,ss,bss) <- fiEqAbVarsJT wlen slen fs ms ps bps
            --Live of passed
            lps <- livePassed (wlen,slen) ss bss
            (wavs,savs,passed) <- fiEqLiveJT wlen slen fs lps lhs
            return ((wavs,savs),IsJT, Just passed,ss,bss)
        | otherwise -> error "!?"
  return FI {
    fiReachable = reachable,
    fiLHS = lhsavs,
    fiBodyInfo = bi,
    fiPassed = mpassed,
    succs = ss,
    preds = ps,
    badFunSuccs = bss,
    badFunPreds = bps
    }
{-
fiEqAbVars
  :: (AIC m, MonadError AIError m,
      MonadReader (OptCore, ModState (S m)) m) =>
     Either
       (BranchValue, OptFunRHS)
       ((Int, Int), [FunVar])
     -> ModState_ (Chan (S m))
     -> FunInfo_ (Chan (S m))
     -> Chan (S m) (Map FunVar BranchType)
     -> Chan (S m) (Map FunVar (Int, Int))
     -> m (([Chan (S m) AbVar], [Chan (S m) AbVar]),
           Maybe (Map Var (Chan (S m) AbVar)),
           Chan (S m) (Map FunVar BranchType),
           Chan (S m) (Map FunVar (Int, Int)))
fiEqAbVars ei_fun_jt ms fi ps bps =
  case ei_fun_jt of
      --f is a function; infer wlen, slen.
      --Need to map Var => abvar chan to ensure each chan is given exactly
      --one AVar.
      Left ((wvs,_,svs),(ops,branch)) -> do
        (lhs,finalVars,ss,bss) <- fiEqAbVarsFun wvs svs ops branch ms fi ps bps
        return (lhs, Just finalVars, ss, bss)
        --f is a JT; use wlen,slen directly to alloc abvar chans.
      Right ((wlen,slen),fs) -> do
        (lhs,ss,bss) <- fiEqAbVarsJT wlen slen fs ms ps bps
        return (lhs,Nothing,ss,bss)
-}
fiEqAbVarsFun c2ls ws ss ops branch ms fi ps bps = do
  --Allocate lhs abvar chans
  lhs@(wchs,schs) <- lhsAbVars ms (length ws, length ss) ps bps
  --Assign them to their corresponding Vars
  let initVars = M.fromList $ zip (ws ++ ss) (wchs ++ schs)
  finalVars <- aiOps c2ls ops initVars
  (ss,bss) <- aiSuccs fi finalVars branch 
  return (lhs,finalVars,ss,bss)
fiEqAbVarsJT wlen slen fs ms ps bps = do
  lhs <- lhsAbVars ms (wlen,slen) ps bps
  ss <- newChan $ M.fromList $ zip fs $ repeat Normal
  bss <- newChan M.empty
  return (lhs,ss,bss)

{-
fiEqLive
  :: (MonadError AIError m, AIC m) =>
     Either
       (BranchValue, OptFunRHS)
       ((Int,Int),[FunVar]) --ignored except for show
     -> FunInfo_ (Chan (S m))
     -> Maybe ([Chan (S m) Bool], [Chan (S m) Bool])
     -> Maybe (Int,Int) --ignored except for show
     -> Maybe (Map Var (Chan (S m) AbVar))
     -> ([Chan (S m) AbVar], [Chan (S m) AbVar])
     -> m (([AVar_ (Chan (S m))], [AVar_ (Chan (S m))]),
           BodyInfo_ (Chan (S m)),
           Maybe
             ([(Chan (S m) Bool, AVar_ (Chan (S m)))],
              [(Chan (S m) Bool, AVar_ (Chan (S m)))]))
fiEqLive ei_fun_jt fi mlps par mbVars lhs =
  case ei_fun_jt of
      Left ((ws,_,ss),(ops,branch)) -> do
        let Just v2abv = mbVars
        let demand = getDemandFromBranch mlps branch
        fiEqLiveFun ws ss ops demand {-branch-} fi mlps v2abv
      --A JT has no ops; its lhs vars are live if any f in fs has a live var
      --at that position. Precondition: all fs have the same arity so one
      --can safely transpose.
      Right ((wlen,slen),fs) -> do
        let Just lps = mlps
        (wavs,savs,passed) <- fiEqLiveJT wlen slen fs lps lhs
        return ((wavs,savs),IsJT, Just passed)
-}
fiEqLiveJT wlen slen fs lps lhs = do
  --lhs, passed are the same AVars
  let (wls,sls) = lps
      (wabvs,sabvs) = lhs
      (wavs,savs) = (zipWith AVar wls wabvs, zipWith AVar sls sabvs)
      passed = (zip wls wavs, zip sls savs)
  return (wavs,savs,passed)
fiEqLiveFun :: AIC m =>
               [Var] --word vars from lhs
            -> [Var] --stack vars from lhs
            -> Maybe ([Var],[Var]) --Passed var names
            -> Map Var (Value, (PrimOp, Value))
            -> Map Var (Maybe [Chan (S m) Bool])
            -- -> Branch
            -> FunInfo_ (Chan (S m))
            -> Maybe ([Chan (S m) Bool], [Chan (S m) Bool])
            -> Map Var (Chan (S m) AbVar)
            -> m
               --LHS
               (([AVar_ (Chan (S m))], [AVar_ (Chan (S m))]),
                --Var, op liveness
                  BodyInfo_ (Chan (S m)),
                 --Passed
                  Maybe
                  ([(Chan (S m) Bool, AVar_ (Chan (S m)))],
                   [(Chan (S m) Bool, AVar_ (Chan (S m)))]))
fiEqLiveFun ws ss mvps ops demandFromBranch
 --branch
  fi
  mlps
  v2abv = do
  --Here we use fi to avoid being careful about definition order.
  let IsFun {fiVars = fivs,
             fiOpsLive = fiol
            } = fiBodyInfo fi
  --The demand per var from the branch
  --if mlps is Nothing, the branch is exiting and all vars in it are
  --live.
  --Bug: I was compiling return ws to jump ws, so the jump was
  --malformed for return ()
  --var => [bool chan], the list of chans var liveness should be or'd
  --with.
  --Why a list rather than a cbOr? It's an opt to avoid an intermediate
  --cbOr; instead a single one is used for branch and op demand.
  --let demandFromBranch = getDemandFromBranch mlps branch
  --The op demand graph:
  --Bug: ofc, if the BB contains no ops but has a nonempty passed,
  --v2ops will not contain all the relevant vars.
  --The actual set of relevant vars is the union of vars in the lhs
  --and in ops.
  let (v2ops,vals) = demandedOps ops
      relevantVs = S.union (S.fromList $ ws ++ ss) (M.keysSet ops)
  --Each v in relevantVs is demanded by op[lhs] for lhs in v2vals[v],
  --as well as each bch in demandFromBranch[v]
  --Splitting out to make it readily testable in Opt.AI.Test:
  (v2live,lhs2live) <- testableCoreLive
    relevantVs v2ops vals fiol (M.map avLive fivs) demandFromBranch
  --Since v2av and v2live are the same shape, it should be possible
  --to do this in O(n) rather than O(n log n)
  let v2av = M.mapWithKey (\v abv -> AVar (index "v2live" v2live v) abv)
             v2abv
      mpassed = case mlps of
                  Nothing -> Nothing
                  Just (wbs,sbs) ->
                    let Just (wps,sps) = mvps
                    in Just (zip wbs $ map (index "wbs" v2av) wps,
                             zip sbs $ map (index "sbs" v2av) sps)
  {-
  if fmap (length***length) mlps /=
     fmap (length***length) mpassed
    then error "Gotcha!!"
    else return ()
-}
  return ((map (index "map v2av ws" v2av) ws,
            map (index "map v2av ss" v2av) ss),
           IsFun {fiVars = v2av,
                  fiOpsLive = lhs2live
                 },
           mpassed
         )
--Because this uses op liveness (fiol) and var liveness (fivs) from the
--fixpoint, it avoids having to define op and var liveness in topological
--order: the circuit is threaded rather than sequential.
--The downside of that is I must unsafeWire to test it.
testableCoreLive relevantVs v2ops vals fiol fivs demandFromBranch = do
  v2live <- M.fromList <$> forM (S.toList relevantVs)
            (\v -> do
                --let dbg msg = if nameOfVar v == "ret!1"
                --              then unsafePrint msg
                --              else return ()
                let vals = maybe [] S.toList $ M.lookup v v2ops
                    live_per_op = map (index "fiol" fiol) vals
                    mbchs = maybe (Just []) id $ M.lookup v demandFromBranch
                --dbg $ "vals: " ++ show vals
                --dbg $ "length live_per_op: " ++ show (length live_per_op)
                --dbg $ "mbchs: " ++ show (fmap (map (const ())) mbchs)
                bch <- case mbchs of
                         --The var is guaranteed to be live (jump/i dest,cond
                         --or revert/return param).
                         Nothing -> {-dbg "Nothing!?">>-} newChan True
                         Just bchs -> --do
                           --dbg "Just :)"
                           cbOr $ live_per_op ++ bchs
                {-if nameOfVar v == "ret!1"
                  then runCB $ do
                  let Just [passed] = mbchs
                  subWhenChan (\b->unsafePrint $ "bch = " ++ show b) bch
                  subWhenChan (\b->unsafePrint $ "passed = " ++ show b)
                      passed
                  return ()
                  else return ()-}
                return (v,bch))
    --Each op lhs is demanded by each v in lhs
  lhs2live <- M.fromList <$> forM (S.toList vals)
              (\lhs -> do
                  let vs = S.toList $ varsIn lhs
                      bchs = map (\v -> index "fivs" fivs v) vs
                  b <- cbOr bchs
                  return (lhs,b))
  return (v2live,lhs2live)

--Bugfix: passed vars from lhs rather than using branch passed
--Simpl: this doesn't need to be monadic; instead use Nothing to represent
--"v is guaranteed to be true". The cbOr can then be entirely avoided in
--v2live when the v is guaranteed to be true.
getDemandFromBranch ::
  Maybe ([v], [v]) -> --live passed (if not exit)
  Branch -> --fun branch
  (Map Var (Maybe [v]))
getDemandFromBranch mlps branch =
  case mlps of
    Nothing ->
      let Just (wes,ses) = exitBranchValue branch
          vset = S.fromList $ wes ++ ses
      in M.fromSet (const Nothing) vset
    --Bugfix: cond, dest from jump/i must always be live.
    Just (wbs,sbs) ->
      let Just (ws,ss) = branchPassed branch
          cond_dest =
            case branch of
              Jump _mode (dest:_,_,_) ->
                [dest]
              Jumpi _elf (dest:cond:_,_,_) ->
                [dest,cond]
          alwaysLive = M.fromSet (const Nothing) $
                       S.fromList cond_dest
      in M.union alwaysLive $ M.map Just $
         demandedPassed (ws,ss) (wbs,sbs)

--A helper that errors with a given error message when k is missing.
--Used to replace M.! (considered harmful).
--Throwing Haskell exceptions deep in the thunk graph is also problematic;
--TODO use MonadError if necessary.
--It is necessary, need to check and report on conditions in the core logic, not
--just this leaf call.
index err k2v k =
  case M.lookup k k2v of
    Nothing -> error $ "Bad index " ++ show (k, M.keys k2v) ++ " @ " ++ err
    Just v -> v

--The number of words and state vars respectively passed by a fun or jt.
--TODO deduplicate with similar code.
passedArity :: Either (BranchValue,OptFunRHS) ((Int,Int),[FunVar]) ->
               Maybe (Int,Int)
passedArity = \case
  Left (_lhs,(_ops,branch)) ->
    (length***length) <$> branchPassed branch
  Right (ar,_) -> Just ar
--A simple utility function. Precondition: all lists are of equal length.
--Not that it's significant for compiler performance, but hopefully GHC
--eliminates the intermediate tuples.
transpose :: [[a]] -> [[a]]
transpose xss = go xss
  where go [] = []
        go ([]:xss) = []:xss
        go xss = uncurry (:) $ go' xss
        --head and tail each (nonempty) list in one pass
        go' [] = ([],[])
        go' ((x:xs):xss) =
          let (heads,tails) = go' xss
          in (x:heads,xs:tails)

--When computing liveness, the last use is handled first.
--Given a function's successors, get the liveness of each var passed.
--This is ~the logic for computing lhs abvars in reverse:
--need to handle normal jumps, call continues and badfun calls.
--f -normal-> g => g.lhs[i] live => f.passed[i] live
--f -continues(args,rets)-> r =>
-- for i >= 0, r.lhs[rets+i] live => f.passed[args+i] live
--f -badfuncont(args,rets)-> r =>
-- f.passed[0..args] live, --since badfun may use any arg and may return
--When a position becomes live, it would be efficient to drop its subscriptions.
--That's challenging because the subMapDelta writes to many inchans.
--TODO rewrite using combinators that accurately track dependencies...
--badfuncont implies continues, so there's no need to repeat the scope linking.
livePassed :: (AIC m, MonadReader (OptCore, ModState (S m)) m) =>
  (Int,Int) ->
  Chan (S m) (Map FunVar BranchType) ->
  Chan (S m) (Map FunVar (Int,Int)) ->
  m ([Chan (S m) Bool],[Chan (S m) Bool])
livePassed (wlen,slen) ss bss = do
  --Can't run askFi in CB ofc...
  fim <- asks $ funInfo . snd
  runCB $ do
    wins <- replicateM wlen $ newInChan False
    sins <- replicateM slen $ newInChan False
    subMapDelta (\f branchType -> do
                    (ws,ss) <- case fiLHS <$> M.lookup f fim of
                                 Nothing -> error "!?"
                                 Just (wavs,savs) ->
                                   return (map avLive wavs, map avLive savs)
                    case branchType of
                      Normal -> do
                        zipWithM_ implies ws wins
                        zipWithM_ implies ss sins
                      Continues (args,rets) -> do
                        let InChan rrc : scopeCaller = drop args wins
                            scopeCallee = drop rets ws
                            --Hack: we obtain retLive directly rather than
                            --via input modstate.
                            retLive = Chan rrc
                        --Liven scope only if ret is live
                        doWhen retLive $
                          zipWithM_ implies scopeCallee scopeCaller
                )
      ss
    --If bss becomes nonempty then args,ret become live; after that you can
    --unsubscribe.
    --We could also obtain args from the branch; the (args,rets) in every
    --key is for the benefit of preds.
    sub <- subChan bss
    whenSub sub (\r2ar ->
                   if M.null r2ar
                   then return ()
                   else do
                     let (_r,(args,_rets)) = head $ M.toList r2ar
                     let args_ret = take args wins
                     mapM (`writeInChan` True) args_ret
                     unSub sub
                )
    return $ freeze (wins,sins)
      where
        --Similar to lubLink (defined in a where), except implies unsubs itself
        --when the premise becomes true.
        a `implies` b = doWhen a $ writeInChan b True
--Helper; todo reuse elsewhere.
--Compiler errors if the function doesn't exist.
askFI :: MonadReader (OptCore, ModState s) m => FunVar -> m (FunInfo s)
askFI f = do
  mfi <- asks (M.lookup f . funInfo . snd)
  case mfi of
    Nothing -> error "!?"
    Just fi -> return fi

--Returns the Value passed by a branch, if any. TODO use to deduplicate.
--Note the Maybe stk is ignored for now.
branchPassed :: Branch -> Maybe Value
branchPassed = \case
  Jump _mode (dest:ws,_,ss) -> Just (ws,ss)
  Jumpi _else_f (dest:cond:ws,_,ss) -> Just (ws,ss)
  --A jump or jumpi with too few word args is a compiler error
  b@Jump{} -> error $ "Malformed jump: " ++ show b
  b@Jumpi{} -> error $ "Malformed jumpi: " ++ show b
  _ -> Nothing
--The vars demanded by an exiting branch; these are guaranteed to be live.
--Returns Nothing if not exiting
exitBranchValue :: Branch -> Maybe Value
exitBranchValue = \case
  Revert v -> Just v
  Return v -> Just v
  Stop v -> Just v
  _ -> Nothing

--Helper for live computation in funs. Given passed, a Core Value (ws,ss) and
--liveness per position (bchs,bchs),
--map Var => bchs of positions which demand it.
demandedPassed :: Value -> ([a],[a]) -> Map Var [a]
demandedPassed (wvs,svs) (was,sas) =
  foldr (\(v,bch) ->
           M.alter (\case Nothing -> Just [bch]
                          Just bchs -> Just $ bch:bchs
                   ) v) M.empty $
        zip (wvs++svs) $ was++sas
--Given an op map, returns the demand graph var => ops and op => vars.
--Since ops are indexed by lhs and the lhs is exactly the vars that demand it,
--the op => vars map is returned as a set lhs.
demandedOps :: Map Var (Value,(PrimOp,Value)) ->
               (Map Var (Set Value), Set Value)
demandedOps ops = foldr (\(lhs,(op,rhs)) (v2vals,lhses) ->
                           if S.member lhs lhses
                           --the op has already been encountered
                           then (v2vals,lhses)
                           --each v in rhs is demanded by op;
                           --op is demanded by each v in lhs
                           --unionWith inserts lhs for each v in a single
                           --traversal.
                           else (M.unionWith S.union
                                 (M.fromSet (const $ S.singleton lhs) $
                                  varsIn rhs)
                                 v2vals,
                                 S.insert lhs lhses))
                  (M.empty,S.empty) $ M.elems ops
--TODO deduplicate
varsIn :: Value -> Set Var
varsIn (ws,ss) = S.fromList $ ws ++ ss

--Given function body, return liveness of vars and passed
--Note AVars don't need unique chans; you can reuse existing ones.

--Complete the var -> abvar map using the lhs as input.
--I could just map rather than eval in topological order, but
--that would require fetching the input vars.
--Post-SSA there should be no var loops, so this should terminate.
{-
State:
chans = initMap : var => abvar chan
Algo:
explore v =
 if v in chans: return chans[v]
 else:
  (lhs,(op,rhs)) = ops[v]
  cr <- mapM explore rhs
  cl <- apply(lhs,op,cr)
  for i in lhs: chans[i] = cl[i]

apply(lhs,op,cr) =
 --errors if missing:
 Just ((argArity,retArity),f) = opBehavior[op]
 error if arities don't match
 opAI (arity lhs) f cr
-}
aiOps :: (AIC m, MonadError AIError m,
          MonadReader (OptCore, ModState (S m)) m) =>
  Map FunVar AbVar -> --codeG => labels
  Map Var (Value,OpE) -> Map Var (Chan (S m) AbVar) ->
  m (Map Var (Chan (S m) AbVar))
aiOps c2ls ops initMap =
  execStateT (mapM_ explore $ M.keys ops) initMap
  where
    explore v = do
      mch <- gets (M.lookup v)
      case mch of
        Just v -> return v
        Nothing ->
          case M.lookup v ops of
            Nothing -> error "Impossible: v comes from M.keys ops"
            Just (lhs,(op,(rws,rss)))
              | Push ser <- op -> do
                  if not $ null $ rws ++ rss
                    then throwError $ BadArity Arg "push"
                         (0,0) (length rws, length rss)
                    else return ()
                  case lhs of
                    ([w],[]) -> do
                      --Look up label => label type map; it's a function to
                      --avoid having to construct a M.union for each push.
                      core <- asks fst
                      let lab2lt = \lab ->
                            case () of
                              _ | M.member lab $ coreDefuns core ->
                                  Just Fun
                                | M.member lab $ coreJTs core ->
                                  Just JT
                                | M.member lab $ coreStatic core ->
                                  Just CodeG
                                | let -> Nothing
                          ei_lab_abvar = pushBehavior lab2lt ser
                      case ei_lab_abvar of
                        Left lab -> throwError $ UndefinedLabel lab
                        Right ab -> do
                          abch <- newChan ab
                          modify (M.insert w abch)
                          return abch
                    (ws,ss) -> throwError $ BadArity Ret "push"
                               (0,0) (length rws, length rss)
              | Op mnemonic <- op -> do
                  rwchs <- mapM explore rws
                  rschs <- mapM explore rss
                  case M.lookup mnemonic opBehavior of
                    Nothing -> throwError $ BadMnemonic mnemonic
                    Just (argArity,retArity,behavior) -> do
                      let actualAA = (length rws, length rss)
                      if argArity /= actualAA
                        then throwError $ BadArity Arg mnemonic
                             argArity actualAA
                        else return ()
                      let actualRA = (length***length) lhs
                      if retArity /= actualRA
                        then throwError $ BadArity Ret mnemonic
                             retArity actualRA
                        else return ()
                      --Apply the op circuit
                      (lwchs,lschs) <- lift $ opAI retArity (behavior c2ls)
                                       (rwchs,rschs)
                      --Assign the resulting channels to the lhs
                      zipWithM_ (\k v -> modify $ M.insert k v)
                        (fst lhs ++ snd lhs) (lwchs ++ lschs)
                      --Look up v, which is now guaranteed to be set
                      gets (flip (index "v from explore") v)
--Given the vars and branch, which gs may f transition to?
--TODO handle badfun: if a call dest mayBeK, the call only has the continues-to
--ret successor, with retval = lub of args U mayBeK.
--Problem: there is no badfun node, nor does it make sense to add one.
--Solution: add BadFunContinue branchType, lhsAbVars handles the return?
--No, because succs is a map and the caller may already continue to ret.
--Alright, so that's one way an edge can have two branchTypes. Since a jump can
--only have one mode and Calling is the only source of multiple bts, it's the
--only way. BEWARE, if future opts break that the design must be revisited.
--For now an additional badFunSuccs : f => g => (args,rets) is sufficient.
--Why should each word of badfun retval be lub of args U mayBeK?
--Because its behavior is arbitrary, but it should not be able to conjure
--labels from nothing.
--For simplicity, badfun is considered not to call any of its arguments.
--That means (coerce 42)(f) is dangerous...
--NOTE: succs should be {} until the BB is reachable.
--Edit: added badFunSuccs
aiSuccs :: (AIC m, MonadReader (OptCore, ModState (S m)) m) =>
  FunInfo (S m) -> Map Var (Chan (S m) AbVar) -> Branch ->
  m (Chan (S m) (Map FunVar BranchType),
     Chan (S m) (Map FunVar (Int,Int))
    )
aiSuccs fi finalVars branch = do
  --Look up JTs map (used in all jumps)
  jtMap <- asks (coreJTs . fst)
  (ssch,bssch) <-
    case branch of
      --A call g,args,ret,scope;
      --for each g <- dest, f makes a normal jump to g
      --for each r <- ret, f continues to r (note for now ret is constant)
      --A call never jumps to a JT.
      --"Call may return" is actually the same as "the ret position is live"!
      --That means I can defer adding the continues return until it becomes
      --live.
      --ret position live ~ ret var live for now, but I might add a getRet
      --primitive in future; safest to use the position.
      Jump (Calling (args,rets)) (dest:args_ret_scope,_,_) -> do
        --for each g <- dest...
        let Just destch = M.lookup dest finalVars
        (fsch,mayBeBad) <- possFunsCircuit jtMap destch
        --for each r <- ret...
        --The ret Var
        let ret:_ = drop args args_ret_scope
            --The ret abvar chan
            Just retch = M.lookup ret finalVars
        (rsch,_) <- possFunsCircuit jtMap retch
        --Look up ret slot live
        let Just (bchws,_) = fiPassed fi
            retLive = map fst bchws !! args
        runCB $ do
          succsIn    <- newInChan M.empty
          badSuccsIn <- newInChan M.empty
          --for each g <- dest, this makes a normal jump to g
          subSetDelta (\g -> modInChan (M.insert g Normal) succsIn) fsch
          --for each r <- ret, this continues to r iff any call returns
          --If dest may be bad, this continues to r via badfun - TODO
          subSetDelta (\r -> do
                          modInChan (M.insert r $ Continues (args,rets))
                            succsIn
                          doWhen retLive $
                            modInChan (M.insert r (args,rets)) badSuccsIn
                      ) rsch
          return $ freeze (succsIn,badSuccsIn)
      --Only case jumps may jump to a JT,
      --but I handle all non-calls uniformly.
      --A walk in the park compared to call; TODO deduplicate
      Jump other (dest:_,_,_) -> do
        let Just destch = M.lookup dest finalVars
        (fsch,_mayBeBad) <- possFunsCircuit jtMap destch
        runCB $ do
          --TODO write better suite of primitives so this can be implemented
          --with a nice map combinator.
          inch <- newInChan M.empty
          subSetDelta (\f -> modInChan (M.insert f Normal) inch) fsch
          --There can be no badfun calls in non-calls
          bss <- newInChan M.empty
          return $ freeze (inch,bss)
      --{else_f | falsy cond} U {f | f <- possFuns dest, truthy cond}
      --For now mayBeBad is ignored, assuming the then and else branches are
      --intraprocedural. FW: add mode info to each branch, share stack suffix
      --computation so "if cond then f() else g() end" can be optimized to
      --jumpi to f and fall through to g.
      Jumpi else_f (dest:cond:_,_,_) -> do
        let Just destch = M.lookup dest finalVars
        (fsch,_mayBeBad) <- possFunsCircuit jtMap destch
        let Just condch = M.lookup cond finalVars
        (truthy,falsy) <- truthyCircuit condch
        runCB $ do
          inch <- newInChan M.empty
          --{else_f | falsy cond}
          doWhen falsy $ modInChan (M.insert else_f Normal) inch
          --{f | ..., truthy cond}
          doWhen truthy $
            subSetDelta (\f ->
                            modInChan (M.insert f Normal) inch)
            fsch
          --There can be no badfun calls in non-calls
          bss <- newInChan M.empty
          return $ freeze (inch,bss)
      --Exiting branches have no successors
      _ -> (,) <$> newChan M.empty <*> newChan M.empty
  --Condition on reachable
  runCB $ do
    ssin <- newInChan M.empty
    bssin <- newInChan M.empty
    doWhen (fiReachable fi) $ do
      subWhenChan (writeInChan ssin) ssch
      subWhenChan (writeInChan bssin) bssch
    return $ freeze (ssin,bssin)

--The Core functions a jump to abvar av may reach; includes badfun.
--jump av may reach {f | f <- v} U {f | jt <- v, f <- jt}, where the JT map
--param provides the mapping from jts to fs they contain.
--Any value other than f or jt is a badfun, but fortunately that has no
--implications for case since jt+ix = {jt,mayBeK} and badfuns are assumed to
--be impossible outside calls (i.e. within intraprocedural control flow).
--Corollary: case on malformed N1 DTs is UB.
--Note: a jt will never be encountered in a call barring UB.
possFuns :: Map FunVar ((Int,Int),[FunVar]) ->
            AbVar ->
            (Set FunVar, --reachable
             Bool        --may be badfun
            )
possFuns jtMap av =
  (funs av `S.union`
   S.unions (S.map (\jt ->
                      case M.lookup jt jtMap of
                        Nothing -> error "!?"
                        Just (_,fs) -> S.fromList fs) $ jts av),
   not (S.null $ codeGs av) || possKs av > None)
--TODO make a class for this pattern where you can choose how deep in the
--structure of A, B in A -> B you replace a with Chan (S m) a
possFunsCircuit :: AIC m =>
  Map FunVar ((Int,Int),[FunVar]) ->
  Chan (S m) AbVar ->
  m (Chan (S m) (Set FunVar), Chan (S m) Bool)
possFunsCircuit jtMap chav =
  runCB $ do
  fsch <- newInChan S.empty
  bch <- newInChan False
  subWhenChan (\av -> do
                 let (fs,b) = possFuns jtMap av
                 modInChan (\/ fs) fsch
                 modInChan (\/ b) bch)
    chav
  return $ freeze (fsch,bch)
--Returns two Boolean chans (truthy,falsy) which indicate whever the abvar
--may be truthy or 0 respectively.
--Minor opt: I could unsub when both become true.
truthyCircuit :: AIC m =>
                 Chan (S m) AbVar ->
                 m (Chan (S m) Bool, Chan (S m) Bool)
truthyCircuit avch =
  runCB $ do
  truthy <- newInChan False
  falsy <- newInChan False
  --TODO make a variant where the callback takes the sub so it can unsub
  --itself?
  --TODO build flexible f lift combinator and use it here
  subWhenChan (\av -> do
                  let (t,f) = truthiness av
                  if t then writeInChan truthy True else return ()
                  if f then writeInChan falsy True else return ()) avch
  return $ freeze (truthy,falsy)
--TODO move to Opt.AbVar?
--Returns whether the av may be true or false respectively, i.e. whether the
--set of values it represents them includes a nonzero or zero value.
--Note truthiness bottom == (False,False); truthiness is monotonic
truthiness :: AbVar -> (Bool,Bool)
truthiness av =
  let hasLabels = not $ S.null $ S.unions [funs av, jts av, codeGs av]
  in ((possKs av > K 0) || hasLabels,
      --All labels are nonzero so they don't help make falsy possible
      case possKs av of
        None -> False
        K n -> n == 0
        All -> True
     )
  
--reachable[f] = any reachable (preds f)
--Taking continues into account:
--reachable[f] = any reachable *and not continues* (preds f)
--If f calls g and continues to r, then that should liven r iff g returns...
--in which case a return BB in g will jump to r, so continues can be ignored.
--If f calls badfun and continues to r, then f reachable implies r reachable
--since badfun has arbitrary return behavior.
--Add Reader (ModState s)?
eqReachable :: AIC m => ModState (S m) -> FunInfo (S m) -> m (Chan (S m) Bool)
eqReachable ms fi =
  let fs = funInfo ms
  --Can't use mapAny because I need to filter first... TODO redesign
  --circuits to be more composable.
  in do fromNormal <-
          runCB $ forAllMap (newInChan False) (preds fi)
          (\inch g branchType ->
             case branchType of
               Normal ->
                 case M.lookup g fs of
                   Nothing -> error "!?"
                   Just gi -> do
                     --Alt implem that cleans up subscription:
                     --doWhen (fiReachable gi) (writeInChan inch True)
                     --That'd likely  actually be costlier since the bool chan
                     --won't be modified afterward anyway.
                     subWhenChan (inch `modWith` (||)) $
                       fiReachable gi
                     return ()
               _ -> return ()
          )
        fromBadfun <- runCB $ forAllMap (newInChan False) (badFunPreds fi)
          (\inch g _args_rets ->
             case M.lookup g fs of
               Nothing -> error "!?"
               Just gi -> do
                 subWhenChan (inch `modWith` (||)) $
                   fiReachable gi
                 return ()
          )
        cbOr [fromNormal,fromBadfun]
    {-setAny (\g ->
               case M.lookup g fs of
                 Nothing -> error "!?"
                 Just gi -> fiReachable gi)
     (preds fi)-}
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
--The continues dataflow is an overapproximation since I don't check whether
--the callee may return.
--Logic for that: follow intraprocedural jumps (which includes continues),
--report true if any may return.


--lhs abvars = elementwise lub of passed of all preds f
--Modification taking continues into account:
--given f lhs = ...
--for each pred g,
-- if branchType is normal then lhs += passed[g] as before
-- else it's continues(args,rets):
--  (drop rets *** id) lhs += (drop (args+1) *** id) passed[g]
--Why args+1? Can't forget the ret param.
--The abvars and liveness per var could be computed in two different passes...
--Since lhs now depends on two maps (preds and badpreds), I can't use
--forAllMap.
lhsAbVars :: AIC m =>
  ModState (S m) -> --FunInfo (S m) -> --TODO add to Reader context?
  (Int,Int) -> --lhs word and state var arity
  Chan (S m) (Map FunVar BranchType) -> --predecessors
  Chan (S m) (Map FunVar (Int,Int)) -> --f's which call badfun and continue here
  m ([Chan (S m) AbVar],[Chan (S m) AbVar])
lhsAbVars ms (lenw,lens) predecessors badPredecessors =
  runCB $ do
  (wins,sins) <- ((,) <$> replicateM lenw (newInChan bottom)
                  <*> replicateM lens (newInChan bottom))
  flip subMapDelta predecessors
    (\f branchType ->
        case M.lookup f $ funInfo ms of
          Nothing -> error "!?"
          Just fi ->
            case fiPassed fi of
              Nothing -> error "An exiting BB has a successor!?"
              Just (bs_ws,bs_ss) ->
                let (ws,ss) = (map (avVal.snd) bs_ws, map (avVal.snd) bs_ss)
                in case branchType of
                     Normal -> do
                       zipWithM_ lubLink ws wins
                       zipWithM_ lubLink ss sins
                     Continues (args,ret) ->
                       --ret scope is linked to f scope recardless of whether
                       --the callee returns; TODO refine using liveness of ret.
                       zipWithM_ lubLink (drop (args+1) ws) (drop ret wins)
     )
  --Only applies to return continuations, but optimization (e.g. eta red)
  --can create new ones; Core has no concept of return continuation status.
  --f calls a badfun which takes args argument words and returns rets words
  --to this function. scope is lub'd with this function's scope; each word of
  --retval = lub (all arg vars) U {mayBeK}
  --Simplification: just set them to {mayBeK} for now; TODO extend.
  flip subMapDelta badPredecessors
    (\f (args,rets) ->
       case M.lookup f $ funInfo ms of
         Nothing -> error "!?"
         Just fi ->
           case fiPassed fi of
             Nothing -> error "An exiting BB made a badfun call!?"
             --Aside: if f makes a badfun call, all its args should be live.
             Just (bs_ws,bs_ss) -> do
               let (ws,ss) = (map (avVal.snd) bs_ws, map (avVal.snd) bs_ss)
               --retval lub= {mayBeK}*
               --Since I ignore the labels passed to the badfun for now, this
               --can be done in a single action rather than via a subscription
               let retval = take rets wins
               mapM_ (modInChan (\/ bottom{possKs=All})) retval
               --As with continues, link f scope to this scope
               --Unlike in continues, badfun always may return
               --TODO deduplicate the link using a f => set (g,linkType)
               --rather than f => g => bt, f => g => (int,int)
               zipWithM_ lubLink (drop (args+1) ws) (drop rets wins))
  return $ freeze (wins,sins)
 {- runCB $ forAllMap
     ((,) <$> replicateM lenw (newInChan bottom)
       <*> replicateM lens (newInChan bottom)) predecessors
     --For each f, look up (ws,ss) = passed[f] and link them to the inchans
     --Note the length of ws may differ from that expected due to call
     --(passes more) or ret (passes less). That's fine, then we simply don't
     --link the excess vars.
     --If branchType is continues (args,rets), link the caller's scope to
     --this return continuation's scope; state vars are not linked.
     --That'll change when I change the state tuple to a stack.
     (\(wins,sins) f branchType ->
        case M.lookup f $ funInfo ms of
          Nothing -> error "!?"
          Just fi ->
            case fiPassed fi of
              Nothing -> error "An exiting BB has a successor!?"
              Just (bs_ws,bs_ss) ->
                let (ws,ss) = (map (avVal.snd) bs_ws, map (avVal.snd) bs_ss)
                in case branchType of
                     Normal -> do
                       zipWithM_ lubLink ws wins
                       zipWithM_ lubLink ss sins
                     Continues (args,ret) ->
                       zipWithM_ lubLink (drop (args+1) ws) (drop ret wins)
     )-}
  where
    lubLink :: (JoinSemilattice a, Eq a) =>
               Chan s a -> InChan s iv a -> CB s iv ()
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
