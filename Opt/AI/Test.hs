{-# LANGUAGE LambdaCase #-}
module Opt.AI.Test where

import Core.RestrictedCore
import Core.SSA (OptCore,OptFunRHS)
import Opt.AI
import Opt.HTraversable (Id(..))

import Data.Map(Map(..))
import qualified Data.Map as M
import Data.Set(Set(..))
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Except
import Control.Monad
import Control.Arrow ((***))

--Discovered bug: livePassed always seems to be False.
--In mstore(0,1);evm_return(0,32):
--evm_return[] and $trueMain have correct live state vars.
--However, mstore[] is reachable but has no live vars.
--In $trueMain, the m var (containing main) is dead; TODO add cond, dest to
--live.
-- $ret not being live in mstore[] perhaps explains part of it.
--I get complaints about unreachable BBs as well... ignore?
--All passed are no longer False, but they're not correct either...
--Potential effect bug: if balance is in other, stop should return it...
--In main():=stop(), in main[()]1,
--the passed is correct (stop live, local, ret dead); (sto,tsto,ext live)
--but lhs is incorrect (ret live);(calldata,returndata live).
--Debugging is difficult because the circuit approach is a very different
--paradigm: while the circuit construction is all in one place, the updates
--are concurrent. I could log the updates and Core constructs they correspond
--to...
--Breaking it up will expose dataflow and simplify the spine.
--Solution to testing issue: separate the a -> b circuit from the logic for
--fetching info from (core,fi); test the circuit in isolation.

--The recursive equation that defines the abstract state is what necessitates
--abstract interpretation via circuits rather than a more conventional monadic
--program a la Fused.
--However, testing the correctness of the end result is much simpler - you
--can just check each step of the equation is satisfied!

--Hunting bug: mstore(0,1);evm_return(0,32) does not consider mstore's args
--live. However, the generated SSA Core for mstore passes the updated $memory
--to the caller, and $memory is live for evm_return. Somewhere the liveness
--equation is violated.
--Another bug: main's $ret is live in main[()], but then it stops being live
--(in the above code, where $ret should be dead from the start).

--The ways the AI equation can be violated.
data Violation = JTLiveness ([Bool],[Bool]) ([Bool],[Bool])
               | LivenessVar Var Bool --the bool is the incorrect value
               | LivenessOp Value Bool
               --Reporting context
               | InLiveness FunVar [Violation]
  deriving (Eq,Ord,Read,Show)
--If there's an unexpected result due to a bug in the test itself, throw
--an error and halt the test; report any violations found until then.
--It might also be triggered by a bug in the Core, e.g. undefined labels.
data AITestError = AITUndefinedLabel String
                 | ExpectedBB String
  deriving (Eq,Ord,Read,Show)
--The type of tests; the Core and its abstract state are passed together.
--It may catch 
type AITest = ReaderT (OptCore,FrozenModState)
              (ExceptT AITestError (Writer [Violation]))
runAITest :: AITest a -> OptCore -> FrozenModState ->
             (Either AITestError a, [Violation])
runAITest ait oc fms =
  runWriter $ runExceptT $ runReaderT ait (oc,fms)

--Runs withinBBLiveness on all BBs
testAllLiveness :: AITest ()
testAllLiveness = do
  (_,ms) <- ask
  --Filtering out unreachable for now...
  let fs = M.keys $ M.filter (unId . fiReachable) $ funInfo ms
  mapM_ withinBBLiveness fs

--Within-BB liveness equation:
--For each f lhs = let ops in branch,
--op live = any produced var live
--1)If branch is an exit, all its vars are live
--2)If jump/i then cond,dest and vars at live position are live
--3)If demanded by live op, var is live
--Live set is closure of those rules starting from 1
--lhs pos live = its var is live.
withinBBLiveness :: FunVar -> AITest ()
withinBBLiveness f = pass $ do
  --Collect all violations and return them as a single InLiveness f
  (_,viols) <- listen go
  return ((), const $ if null viols
                      then []
                      else [InLiveness f viols])
  where go =
          do
            lthing <- getBB f
            case lthing of
              AFun (lhs,(ops,branch)) fi -> do
                --The set of vars demanded by the branch
                let bvs = liveBranch fi branch
                    --If op is live, its rhs is live
                    op2vs = M.map (varsIn . snd) $ M.fromList $ M.elems ops
                    --If v is live, its op is live
                    v2op = M.map (\(lhs,_) -> lhs) ops
                    --I didn't really need to convert bvs to a set since
                    --explore is
                    --idempotent... but minimizing state is good practice.
                    (vs,lhses) = depGraph2Live op2vs v2op bvs
                --Each v in fiVars is live iff it's in vs
                --Each op in fiOpsLive is live iff it's in lhses
                let IsFun {fiVars = fvs, fiOpsLive = fiol} = fiBodyInfo fi
                forM_ (M.toList fvs)
                  (\(v,avar) -> do
                      let Id live = avLive avar
                      reportIf (live /= S.member v vs) $ LivenessVar v live
                  )
                forM_ (M.toList fiol)
                  (\(lhs,Id live) ->
                     reportIf (live /= S.member lhs lhses) $ LivenessOp lhs live
                  )
              --LHS liveness should equal passed liveness
              AJT fs fi -> do
                let lhsLiveness = liveLHS fi
                    Just passedLiveness = aitLivePassed fi
                reportIf (lhsLiveness /= passedLiveness)
                  $ JTLiveness lhsLiveness passedLiveness
--(op => vars it demands, var => op it demands) -> vars demanded by branch ->
--live vars, live ops.
depGraph2Live :: Map Value (Set Var) -> Map Var Value -> Set Var ->
  (Set Var, Set Value)
depGraph2Live op2vs v2op bvs =
  execState (mapM_ (explore op2vs v2op) $
             S.toList bvs)
  (S.empty,S.empty)
  where explore :: Map Value (Set Var) -> Map Var Value -> Var ->
          State (Set Var, Set Value) ()
        explore op2vs v2op v = do
          (vs,lhses) <- get
          if S.member v vs
            --v already live
            then return ()
            else do
            modify (S.insert v *** id)
            case M.lookup v v2op of
              --The var must be from lhs
              Nothing -> return ()
              --v bound by op; liven op
              Just lhs -> exploreOp op2vs v2op lhs
        exploreOp op2vs v2op lhs =
          case M.lookup lhs op2vs of
            Nothing -> error "!?"
            Just vs -> do
              modify (id *** S.insert lhs)
              forM_ (S.toList vs) $ explore op2vs v2op
liveLHS :: FrozenFunInfo -> ([Bool],[Bool])
liveLHS = both (map $ unId . avLive) . fiLHS
aitLivePassed :: FrozenFunInfo -> Maybe ([Bool],[Bool])
aitLivePassed = ((both (map $ unId . fst))<$>) . fiPassed
both f = f *** f

liveBranch :: FrozenFunInfo -> Branch -> Set Var
liveBranch fi = \case
  Jump _mode (dest:ws,_,ss) -> S.insert dest $ go ws ss
  Jumpi _elf (cond:dest:ws,_,ss) -> S.insert cond $ S.insert dest $ go ws ss
  Revert val -> varsIn val
  Return val -> varsIn val 
  Stop val -> varsIn val
  where go ws ss =
          let Just (lws,lss) = aitLivePassed fi
          in S.fromList [v | (True,v) <- zip (lws ++ lss) $ ws ++ ss]
{-
invertRelation :: (Ord k, Ord v) => Map k (Set v) -> Map v (Set k)
invertRelation k2vs =
  let vks = do
        (k,vs) <- M.toList k2vs
        v <- S.toList vs
        return (v,k)
  in foldr (\(v,k) -> M.alter (Just . maybe (S.singleton k) (S.insert k)) v)
     M.empty vks
-}
--Compute inverse dependency graph var => set op; TODO reuse 
--TODO: given passed and branch, get live var set
--Implement as exploration alongside livening internal vars and ops
        
--Computing liveness here will duplicate a lot of logic in Opt.AI, but
--that's unavoidable. Hopefully bugs in the AI and test are uncorrelated!

data LabeledThing = AFun (BranchValue,OptFunRHS) FrozenFunInfo
                  | AJT ((Int,Int),[FunVar]) FrozenFunInfo
                  | ACodeG --No detailed info for now
reportIf :: Bool -> Violation -> AITest ()
reportIf b viol = if b then tell [viol] else return ()
getLabel :: FunVar -> AITest LabeledThing
getLabel nm = do
  (core,ms) <- ask
  let mfi = M.lookup nm $ funInfo ms
  case () of
    _ | Just fdef <- M.lookup nm $ coreDefuns core ->
        case mfi of
          Nothing -> error "!?"
          Just fi -> return $ AFun fdef fi
      | Just ar_fs <- M.lookup nm $ coreJTs core ->
        case mfi of
          Nothing -> error "!?"
          Just fi -> return $ AJT ar_fs fi
      | Just _ <- M.lookup nm $ coreStatic core ->
        return ACodeG
      | let -> throwError $ AITUndefinedLabel nm
getBB :: FunVar -> AITest LabeledThing
getBB f = do
  thing <- getLabel f
  --Using case rather than == to future-proof vs changes to ACodeG
  case thing of
    ACodeG {} -> throwError $ ExpectedBB f
    _ -> return thing

--TODO check: do I liven cond and dest when they're branched on?
--The lives seem to be in the correct order: evm_return considers arg 1 and 2
--live, but not $ret.

--var x = 1; x = x & x; evm_return(x,x)
--considers main[()]1 to have a live $ret, but not its callee main[()]2
-- $ret shouldn't be live at all.

--Useful debugging queries:
liveWordsLHS f ms = map avLive $ fst $ fiLHS $ funInfo ms M.! f
liveWordsPassed f ms =
  ((map fst . fst) <$>) $ fiPassed $ funInfo ms M.! f
--This shouldn't happen!
allPassedFalse ms =
  all (\fi ->
         case aitLivePassed fi of
           Nothing -> True
           Just (ws,ss) -> not $ or $ ws ++ ss) $
  funInfo ms
