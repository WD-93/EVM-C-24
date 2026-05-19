{-# LANGUAGE LambdaCase #-}
module Opt.CC where

import Core.RestrictedCore
import Core.SSA (OptCore())
import Opt.AI
import Opt.HTraversable (Id(..))

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad (forM,forM_)

--The pruneDeadOps opt rule eliminates nontrivial dead ops, but trivial values
--(0 for stack words, empty* for state vars) still need to be passed to
--continuation params in the branch in order to ensure the arguments match the
--shape of the callee's lhs.
--That interferes with eta reduction, since f lhs = g dead:lhs is not
--recognized as reducible due to the stack shape changing.
--It would be nice to prune dead params from Core function lhses, but there's
--an issue: if the lhs shape is changed, all call sites must change as well.
--Furthermore, if f -> g or h, g's shape can't be safely changed without
--performing the same change for h.
--Solution: before pruning dead params, functions must be grouped into
--calling conventions (CCs), consisting of an argument shape, caller set and
--callee set.
--For a given CC with shape (ws,ss), to safely reorder or prune its
--arguments you must perform the same transformation at all call sites and
--callee lhses.
--Opt 1: if a param x is dead at all call sites (or equivalently, all callee
--lhses), prune it.
--FW Opt 2: if params x,y,z,... are always equal at all call sites, prune all
--but the first.
--FW: support reordering params if it improves gas efficiency of peeped
--bytecode.
--NOTE: to prune state vars, I need to change the logic in AI that assumes
--all are always passed and that the pos of a state var of a given type can be
--inferred from envV.

--How to determine two vars x, y in a BB are equal (x ~ y)?
--Simple cond:
--x == y, or
--x, y have equal constant abstract values, or
--x = op1 xs, y = op2 ys s.t. op1 == op2, xs ~ ys

--Partitioning funs into CCs requires unifying them.
--If f -> g, then exists cc s.t.
--callerCC[f] = cc && calleeCC[g] = cc && f elem callers(cc) && g elem
--callees(cc) && shape(cc) = arity g.
--Since C calls may be to functions with bad arities, we restrict CC-based
--opts to intraprocedural jumps at first. TODO treat bad arities as UB and
--ignore their possibility in AI.

cc :: FrozenModState -> OptCore -> CCPartition
cc ms core =
  let fgs = ccEquations ms core
      ccs = execState (do mapM_ (uncurry calls) fgs
                          normalizeCCS) CCS{ccsCaller=M.empty,
                                            ccsCallee=M.empty
                                           }
  in ccPartition ms ccs

{-
Unification algo: key CCs by highest caller fun.
State:
caller : f => f
callee : g => f
Instead of trampolining (as I do in HM; TODO opt), adjust during lookup a la
union-find. The representative f has no entry in the mapping.
Once unification is complete, infer ccs : f => (callers,callees,shape)
-}

data CC = CC {
  ccCallers :: Set FunVar,
  ccCallees :: Set FunVar,
  ccShape :: (Int,Int)
  }
  deriving (Eq,Ord,Read,Show)
--Representative caller => CC
type CCPartition = Map FunVar CC
data CCS = CCS {
  ccsCaller :: Map FunVar FunVar,
  ccsCallee :: Map FunVar FunVar
  }
  deriving (Eq,Ord,Read,Show)
type CCM = State CCS
unify :: FunVar -> FunVar -> CCM ()
unify f1 f2 = do
  r1 <- getCaller f1
  r2 <- getCaller f2
  unifyR r1 r2
--Unify two representatives; the largest one is dominant
unifyR :: FunVar -> FunVar -> CCM ()
unifyR r1 r2 =
  case () of
    --Nothing to do, they're already unified
    _ | r1 == r2 -> return ()
      | r1 > r2 -> setCaller r2 r1
      | let -> setCaller r1 r2
--Helpers
setCaller :: FunVar -> FunVar -> CCM ()
setCaller k v =
  modify $ \ccs->ccs{
             ccsCaller = M.insert k v $
                         ccsCaller ccs
             }
setCallee :: FunVar -> FunVar -> CCM ()
setCallee k v =
   modify $ \ccs->ccs{
             ccsCallee = M.insert k v $
                         ccsCallee ccs
             }

--f -> g => callee g = caller f
--If g does not yet have a CC, set it to caller f
calls :: FunVar -> FunVar -> CCM ()
calls f g = do
  rf <- getCaller f
  mrg <- getCallee g
  case mrg of
    Nothing -> setCallee g rf
    --callee[g] is never updated; getCaller ensures the chain
    --f = callee[g] => caller[f] remains short. 
    Just f' -> unifyR f f'

--Follow the ccsCaller chain until the representative f is found, then return
--it and update caller[f] for each f in the chain.
getCaller :: FunVar -> CCM FunVar
getCaller = go
  where go f = do
          caller <- gets ccsCaller
          case M.lookup f caller of
            --f is the representative element
            Nothing -> return f
            Just f' -> do
              repr <- go f'
              setCaller f repr
              return repr
--A callee may not yet belong to a CC, but since it's not a representative
--we should return Nothing in that case.
--Does not need to lazily update callee[g]: that's a log n operation, the
--same cost as the lookup on f.
getCallee :: FunVar -> CCM (Maybe FunVar)
getCallee g = do
  callee <- gets ccsCallee
  case M.lookup g callee of
    Nothing -> return Nothing
    Just f -> Just <$> getCaller f

--After all equations have been applied, normalize the CCS to simplify
--extraction of the CCPartition:
--Postcond: each caller f and callee g in the map points to its repr
normalizeCCS :: CCM ()
normalizeCCS = do
  fs <- M.keys <$> gets ccsCaller
  forM_ fs (\f -> getCaller f >>= setCaller f)
  gs <- M.keys <$> gets ccsCallee
  forM_ gs (\g -> do
               mrf <- getCallee g
               --It's guaranteed to have a representative
               let Just rf = mrf
               setCallee g rf)

--CCM only concerns itself with a list of f->g equations; to produce them we
--must parse the analyzed Core.
--We consider only intraprocedural jumps:
--Jump Intraprocedural and Jumpi (which is always IP for now).
--A jump into a JT is considered an IP jump with succs = fs in the JT; since
--the JT is not considered a successor we don't need to parse it.
--Using M.intersectionWith to avoid the log n factor from looking up the
--funInfo element for each Core IP BB; TODO use the same trick elsewhere.
--Actually, I only need the fi...
ccEquations :: FrozenModState -> OptCore -> [(FunVar,FunVar)]
ccEquations ms core =
  --The Core BBs which perform IP jumps in their branch
  let ipBBs = M.keysSet $ M.filter (\(_lhs,(_ops,branch)) -> isIP branch) $
              coreDefuns core
      ipFIs = M.restrictKeys (funInfo ms) ipBBs
      f2gs = M.mapWithKey (\f fi -> map ((,) f) $ M.keys $ unId $ succs fi)
             ipFIs
  in concat $ M.elems f2gs
  where isIP = \case
          Jump Intraprocedural _ -> True
          Jumpi {} -> True
          _ -> False

--Once the equations have been solved, it's time to convert the CCS into
--a CC partition:
{-
For each caller[f]=rf:
 if rf not yet in the partition:
  rf.shape = passed of f
  rf.callers = {}
  rf.callees = {}
 rf.callers += f
For each callee[g]=rf:
 rf.callees += g
-}
ccPartition :: FrozenModState -> CCS -> CCPartition
ccPartition ms ccs =
  execState (do let caller = ccsCaller ccs
                forM_ (M.toList caller)
                  (\(f,rf) -> do
                      initRF rf
                      addCaller rf f)
                let callee = ccsCallee ccs
                forM (M.toList callee)
                  (\(g,rf) -> addCallee rf g)) M.empty
  where
    initRF :: FunVar -> State CCPartition ()
    initRF rf = do
      ccp <- get
      if M.member rf ccp
        then return ()
        else put $ M.insert rf CC{ccCallers = S.empty,
                                  ccCallees = S.empty,
                                  ccShape = shape rf
                                 }
             ccp
    addCaller :: FunVar -> FunVar -> State CCPartition ()
    addCaller rf f =
      modify $ M.adjust (\cc->cc{ccCallers=S.insert f $
                                           ccCallers cc})
      rf
    addCallee :: FunVar -> FunVar -> State CCPartition ()
    addCallee rf g =
      modify $ M.adjust (\cc->cc{ccCallees=S.insert g $
                                           ccCallees cc})
      rf
    --rf is a caller and is either a jump or jumpi
    shape rf =
      case M.lookup rf $ funInfo ms of
        Nothing -> error "!?"
        Just fi ->
          let Just (ws,ss) = fiPassed fi
          in (length ws, length ss)
