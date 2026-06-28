{-# LANGUAGE LambdaCase, PatternSynonyms,
 StandaloneDeriving, TypeSynonymInstances, FlexibleInstances, DeriveDataTypeable
#-}
module Opt.Opt where

import Core.RestrictedCore
import Opt.AI hiding (unsafePrint,debugFlag)
import Core.SSA (OptCore(),OptFunRHS(),OpMap())
import Util ((?))
import Const.Const
import Opt.HTraversable (Id(..))
import Opt.Analysis.Exitness (Exitness(..),analyzeExitness)
import Core.PrimTypes
import AST.DTs (pattern Memory, pattern UInt)
import Opt.AbVar --for control flow DCE, CE
import Opt.CC --for param DCE
import Util (unsafePrint')

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Generics
import Control.Monad
import Control.Monad.State
import Control.Arrow ((***))

debugFlag = True
unsafePrint str = unsafePrint' debugFlag str

--Opt errors are compiler errors
data OptError = OptAIError AIError
  deriving (Eq,Ord,Read,Show)
--I'll need to repeatedly run ai.
opt :: OptCore -> Either OptError OptCore
opt core = do
  core' <- iteratively optimize core
  unsafePrint $ "opt done; length show core' = " ++ show (length $ show core')
  return core'

--Apply transformation until error or convergence
iteratively :: Eq a => (a -> Either err a) -> a -> Either err a
iteratively f = go
  where go a = do
          unsafePrint "iteration!"
          a' <- f a
          unsafePrint "iteration done!"
          if a == a'
            then do
            unsafePrint "a == a'"
            return a
            else do
            unsafePrint "a /= a'"
            go a'

--Problem: AI is expensive, so we want to perform it as rarely as possible.
--However, opt rules may invalidate the results.
--For now I'll redo AI whenever a rule fires rather than try to be clever.
optimize :: OptCore -> Either OptError OptCore
optimize core = do
  ms <- ai core ? OptAIError
  unsafePrint "Starting opt!"
  applyRules ms core [("pruneUnreachableFuns",
                       pruneUnreachableFuns)
                      ,("revertDivergent",
                        revertDivergent)
                      ,("etaReduction",
                        etaReduction)
                      ,("pruneDeadOps",
                        pruneDeadOps)
                      ,("controlFlowDCE",
                        controlFlowDCE)
                      ,("pruneParams",
                        pruneParams)
                      --,("inlining",
                      --  inlining)
                      ,("constantExpansion",
                        constantExpansion)
                     ]
--Invariant: ms pertains to core
applyRules ms core [] = do
  unsafePrint "No more rules"
  return core
applyRules ms core ((description,rule):rules) = do
  unsafePrint description
  core' <- rule ms core
  unsafePrint $ "done with " ++ description
  unsafePrint $ "length $ show core': " ++ show (length $ show core')
  if core == core'
    then do
    unsafePrint "It didn't change!"
    applyRules ms core rules
    --Return to iteratively, which recomputes ms via optimize
    else return core'

type OptRule = FrozenModState -> OptCore -> Either OptError OptCore
--For debugging: apply a list of rules so I can step through the opt process
--and see where etaReduction with eta-reducible fs deleted goes wrong.
dbgApplyRules :: [OptRule] -> OptCore -> Either OptError OptCore
dbgApplyRules [] core = return core
dbgApplyRules (rule:rules) core = do
  ms <- ai core ? OptAIError
  core' <- rule ms core
  dbgApplyRules rules core'

--AI gives an upper bound on behavior; if a Core function is unreachable it
--will never become reachable.
--A function may be mentioned in push ops, but never called. Any mention should
--be replaced with 0x0001 to ensure labels are always nonzero (assumed by AI).
--Pruning before substitution avoids wasted substitution work.
--JTs are part of funInfo, so they can be pruned as well.
--A JT is always jumped into in the BB that mentions it, so if it's
--unreachable then its parent BB is as well. That means it'll never need to
--be substituted.
pruneUnreachableFuns :: OptRule
pruneUnreachableFuns ms core =
  let unreachableFuns = unreachable coreDefuns
      unreachableJTs = unreachable coreJTs
      --Short-circuiting: if there's nothing to prune don't traverse
  in if S.null unreachableFuns && S.null unreachableJTs
     then return core
     else return $ substUnreachable unreachableFuns core{
    coreDefuns = filterKeys (not . flip S.member unreachableFuns) $
      coreDefuns core,
    coreJTs = filterKeys (not . flip S.member unreachableJTs) $
      coreJTs core
    } --filterKeys on S.member adds a log n factor... TODO exploit shared
      --structure.
  where unreachable field =
          S.filter (\f ->
                      case M.lookup f $ funInfo ms of
                        Just fi -> not $ unId $ fiReachable fi
                        Nothing -> error "!?"
                   ) $
          M.keysSet $ field core
--M.filterKeys requires containers>=0.8... writing an inefficient replacement
--for now.
filterKeys :: Ord k => (k -> Bool) -> Map k a -> Map k a
filterKeys f = M.fromList . filter (f . fst) . M.toList

--Unreachable function labels are present only in map keys (where they'll
--be filtered out) and Serialized values in pushes and staticData.
--In all Serialized values: substitute each Right (0,2,deadf) for Left [0,1],
--then normalize to coalesce adjacent bytestring regions.
--Problem: that might affect the byte length of static data... need to ensure
--it's aligned correctly afterward.
--Bugfix: label uses do not necessarily have (off,len) == (0,2), consider
--a constructor tag = Struct(f,0 :: UInt 31). That will split the function f
--over two words!
--For now I'll assume labels are originally 16b before they're sliced;
--imported labels may change that in future.
substUnreachable :: Data a => Set FunVar -> a -> a
substUnreachable ur = everywhere (mkT go)
  where go :: Serialized -> Serialized
        go ser = ser{serContent = normalizeContent $
                      map (\case Right (off,len,lab) ->
                                     if S.member lab ur
                                     --Will break if unreachable labs are
                                     --ever permitted to be >2B
                                     then Left $ take len $ drop off [0,1]
                                     else Right (off,len,lab)
                                 x -> x) $
                      serContent ser
                    }
deriving instance Data OptCore

--Goal for minimal optimizer:
--DCE, CE, inlining, eta reduction, BB-local symbolic opt

--Using Opt.Analysis.Exitness.analyzeExitness, identify infinite loops and
--replace them with revert(0,0).
revertDivergent :: OptRule
revertDivergent ms core =
  let f2e = analyzeExitness ms core
      divergent = M.keysSet $ M.filter (==Bottom) f2e
      --Substitute all fs in divergent for revert(0,0)
      --It's fine to leave JTs unchanged, since if it's divergent
      --then the BB that jumps into it must be as well and so it'll no longer
      --be reachable.
      --Since this only modifies bodies, there's no risk of invalidating
      --mentioned function names.
  in return core{coreDefuns =
                    M.mapWithKey (\f (lhs,rhs) ->
                                    (lhs, if S.member f divergent
                                          then revert_0_0 lhs
                                          else rhs)) $
                    coreDefuns core
                }
  where
    --let z = push 0; m = emptyMem in revert ([z,z],[$mem])
    --Problem: if mem is dead in the divergent BB, it may not be available.
    --Fortunately, revert(0,0) doesn't really need memory... but I need to add
    --an emptyMem op!
    --I also need to ensure z and m don't conflict with any vars in lhs.
    revert_0_0 lhs =
      --Alloc new names:
      --Precondition: there are no Vars with the same name but different types
      let (ws,_,ss) = lhs
          vs = S.fromList $ map nameOfVar $ ws ++ ss
          [z,m] = evalState (mapM allocName ["z","m"]) vs
          zv = Mono z (W (UInt 32) 1)
          mv = Mono m Memory
      in (M.fromList [ --let
             --z = push 0
             (,) zv $ (,) ([zv],[]) $
               (,) (Push Serialized{serLength=0,serSizeof=0,serContent=[]})
               ([],[])
             ,(,) mv $ (([],[mv]), (Op "emptyMem", ([],[])))
             ],
          --in revert (z,z);m
          Revert ([zv,zv],[mv])
         )
--When adding new ops to a BB (e.g. when replacing an infinite loop with
--revert(0,0) or inlining), we need to allocate names not already bound.
--That can be done locally (without a global counter) by trying variants of
--a name until you find one not in the set.
--I do that naively by trying x, x1, x2, ... for nm param x.
--That's not very efficient (worst case n*log n*length x), but vars are short
--in practice and string processing is unlikely to be the dominant cost
--factor.
allocName :: String -> State (Set String) String
allocName nm = do
  taken <- get
  go taken $ nm : [nm ++ show n | n <- [1..]] 
 where
   go :: Set String -> [String] -> State (Set String) String
   go taken (nm:nms) =
     if nm `elem` taken
       then go taken nms
       else do
       modify $ S.insert nm
       return nm
--DCE:
--Control flow: prune unreachable funs, ifte->jump, case->jump

--ifte on known cond => jump, ifte with same dest in both cases => jump
--case: jump (jt+5k) => jump jt[k].
{-
jumpi destv,cond,rest s.t. truthiness abvar cond = (True,False) =>
 jump ipc dest,rest
jumpi dest,cond,rest else elf s.t. ditto = (False,True) =>
 add elfv = elf to ops, jump ipc elfv,rest
jumpi destv,cond,rest else elf s.t. abvar destv == label Fun elf =>
 jump ipc destv,rest
jump dest,rest s.t. dest = a + b, abvar a == label JT jt, abvar b == exactly 5k
 => look up fs of jt. If k in range, add op dest' = fs[k], else revert (UB).
-}
controlFlowDCE :: OptRule
controlFlowDCE ms core =
  return core{coreDefuns = M.mapWithKey
             (\f def@(flhs,(opMap,branch)) ->
                (,) flhs $
                case branch of
                  Jumpi else_f (dest:cond:rest,mstk,ss) ->
                    case M.lookup f $ funInfo ms of
                      Nothing -> error "!?"
                      Just fi ->
                        --Check for known cond:
                        let v2av = fiVars $ fiBodyInfo fi
                            Just avcond = M.lookup cond v2av
                            abvcond = unId $ avVal avcond
                            (t,f) = truthiness abvcond
                        in case (t,f) of
                             (True,False) ->
                               (opMap, Jump Intraprocedural (dest:rest,mstk,ss))
                             (False,True) ->
                               --Here I need to add a push else_f op.
                               let scope = S.map nameOfVar $ M.keysSet v2av
                                   elf' = evalState (allocName else_f) scope
                                   elfv = dest{nameOfVar=elf'}
                                   elfop = (([elfv],[]),
                                            (Push Serialized{
                                                serLength=2,
                                                serSizeof=2,
                                                serContent=[Right(0,2,else_f)]
                                                },
                                              ([],[])))
                               in (M.insert elfv elfop opMap,
                                   Jump Intraprocedural (elfv:rest,mstk,ss))
                             --No known cond, try for equal branches:
                             _ ->
                               let Just avdest = M.lookup dest v2av
                                   abvdest = unId $ avVal avdest
                               in case unlabel abvdest of
                                    Just (_,then_f)
                                      --If this is true then_f is necessarily
                                      --a Fun:
                                      | then_f == else_f ->
                                        (opMap, Jump Intraprocedural
                                          (dest:rest,mstk,ss))
                                    _ -> (opMap,branch)
                  --Jump Intraprocedural bv -> error "todo"
                  _ -> (opMap,branch)
                  )$
             coreDefuns core
             }

--First divide intraprocedural callers and callees into calling conventions
--(CCs) whose params must be jointly modified.
--For now, just prune dead params in words; state remains unchanged and
--is therefore always the same as envV (modulo SSA versions).
--To change state, need to modify the logic for getting and setting state
--params in AI.
--For each CC, liveness = lub of liveness of each caller (for words)
--If any pos in liveness is false, update branch params of all callers to
--filter out the dead var; update lhs of all callees as well.
--Annoyance: I already discarded the f => cc, g => cc maps!
--TODO modify CC; until then just reconstruct.
--Each f is caller of at most one scc and callee of at most one scc (they
--may be different).
--BUG: If a f in a CC is C-called, the entire CC must be fixed, but this may
--change it. That may occur if a function starts with a while loop.
--TODO filter out C-called CCs in Opt.CC.
pruneParams :: OptRule
pruneParams ms core = do
  let ccs = cc ms core
      r2live_fs_gs =
        M.map (\cc -> (livenessCC cc, ccCallers cc, ccCallees cc)) ccs
      --Implicitly reconstructing f => cc:
      f2live =
        M.unions $ map (\(live,fs,_) -> M.fromSet (const live) fs) $
        M.elems r2live_fs_gs
      g2live =
        M.unions $ map (\(live,_,gs) -> M.fromSet (const live) gs) $
        M.elems r2live_fs_gs
  --unsafePrint $ "ccs: " ++ show ccs
  --unsafePrint $ "f2live: " ++ show f2live
  return core{
    coreDefuns =
        M.mapWithKey (\f (lhs,(ops,branch)) ->
                         let lhs' = case M.lookup f g2live of
                                      Just live -> updLHS live lhs
                                      Nothing -> lhs
                             branch' = case M.lookup f f2live of
                                         Just live -> updBranch live branch
                                         Nothing -> branch
                         in (lhs',(ops,branch'))) $
        coreDefuns core
    }
  where livePassed :: FunVar -> [Bool]
        livePassed f =
          case M.lookup f $ funInfo ms of
            Nothing -> error "!?"
            Just fi ->
              let Just (pws,_pss) = fiPassed fi
              in map (unId . fst) pws
        --The lub of livePassed of all fs
        livenessCC :: CC -> [Bool]
        livenessCC CC{ccShape = (warity,_), ccCallers = fs} =
          foldr (zipWith (||)) (replicate warity False) $
          map livePassed $ S.toList fs
        updLHS liveness (ws,mstk,ss) =
          (map snd $ filter fst $ zip liveness ws, mstk, ss)
        --Only applies to IP branches:
        updBranch liveness = \case
          Jump Intraprocedural (dest:ws,mstk,ss) ->
            let (ws',_,_) = updLHS liveness (ws,mstk,ss)
            in Jump Intraprocedural (dest:ws',mstk,ss)
          Jumpi elf (dest:cond:ws,mstk,ss) ->
            let (ws',_,_) = updLHS liveness (ws,mstk,ss)
            in Jumpi elf (dest:cond:ws',mstk,ss)
          _ -> error "!?"

--Ops: prune dead ops unless 0 and passed to dead params; if dead and passed
--to dead param replace with 0. The zeroes will be eliminated later if
--possible: that requires assigning callers and callees to calling conventions
--and eliminating params that are dead for all callees in the CC.

--Ops are keyed by lhs.
--For f in coreDefuns, the lhses are the keys of fiOpsLive.
--If an op is dead, but not trivial and used in a dead param, then it can
--be pruned. The trivial ops are 0 for stack vars and empty* for state vars.
--If a dead 0 is used across several dead params, it will be split into
--one 0 for each.
--We ensure other dead ops used by dead params can be pruned by replacing
--the vars used in the branch with new vars bound to trivial ops.
--The "is not trivial" condition prevents a loop where trivial ops are
--endlessly replaced with new ones.
--Exiting branches have no passed liveness info, but that's fine because all
--vars are live.
--New cond: if an op is dead and is not a trivial op passed to a dead branch
--param position, prune it.
--Need to look at branch and opMap together:
--if w = ws[i] is dead and its op is not push 0, add a new w' = push 0 and
--replace with w'
--if s = ss[i] is dead and its op is not trivial(typeOfVar s), add a new
--s' = trivial and replace with s'.
--If branch is an exit, just prune all dead ops
--Keep a set of vars already used as dead trivial in branch so you can alloc
--new ones.
pruneDeadOps :: OptRule
pruneDeadOps ms core =
  return core{
  coreDefuns =
      M.mapWithKey
      (\f (flhs,(opMap,branch)) ->
          case M.lookup f $ funInfo ms of
            Nothing -> error "!?"
            Just fi ->
              let op2live = fiOpsLive $ fiBodyInfo fi
                  deadOps = M.keysSet $
                            M.filter (not . unId) op2live
                  --If branch is an exit, prune all dead
                  (opMap',branch') =
                    case branchPassed branch of
                      Nothing ->
                        (M.filter (\(lhs,_opE) ->
                                     not $ S.member lhs deadOps)
                          opMap,
                         branch)
                      Just val ->
                        --Liveness of passed vars:
                        let Just (pws,pss) = fiPassed fi
                            (lws,lss) = (map (unId.fst) pws,
                                         map (unId.fst) pss)
                            (val',ATS{atsOpMap = opMap',
                                      atsEncountered = ops
                                     }) =
                              runState (allocTrivialAlgo val (lws,lss)) ATS{
                              --Names of vars in lhs and opMap
                              atsScope = S.map nameOfVar $ M.keysSet $ fiVars $
                                fiBodyInfo fi,
                              atsOpMap = opMap,
                              atsEncountered = S.empty
                              }
                        in (M.filter (\(lhs,_opE) ->
                                        not $ S.member lhs $
                                        S.difference deadOps ops)
                             opMap',
                             setPassed val' branch
                           )
              in (flhs, (opMap', branch'))) $
      coreDefuns core
  }
  where
    --Sets the passed value for jump/i; dest,cond remain unchanged.
    --mstk also remains unchanged.
    setPassed (ws,ss) = \case
      Jump mode (dest:_,mstk,_) ->
        Jump mode (dest:ws,mstk,ss)
      Jumpi else_f (dest:cond:_,mstk,_) ->
        Jumpi else_f (dest:cond:ws,mstk,ss)

--A branch either exits or continues. If it continues, it has a passed Value.
--Some of those vars may be at dead param positions. Those need to
--be replaced with new vars bound to trivial ops (push 0 for stack words,
--empty* for state vars).
--Reusing the original var name doesn't work, because a var x at a dead
--position may still be bound by a live op that shouldn't be pruned.
{-
Algo:
scope = vars in lhs and opmap
ops = initial ops (no pruning done)
for each v, poslive:
 if poslive || opMap[v] == trivialOp v:
  return v
 else:
  v' = allocTrivial v
allocTrivial v =
 op = trivialOp v
 v' = allocVar v
 ops[v'] = v'=op
allocVar v =
 nm = allocName with state = scope
 return v{nameOfVar=nm}
Return scope, triv, v's list
Postcondition: if an op is dead, nontrivial and not used by the branch,
it can be safely removed.
-}
--Alloc trivial ops monad
data ATS = ATS {
  atsScope :: Set String,
  --The set of trivial op lhses in the new branchValue so far;
  --ensures zeroes passed as dead params aren't shared.
  --Also used to distinguish between dead and prunable vars;
  --prunable = dead \ encountered
  atsEncountered :: Set Value, 
  atsOpMap :: OpMap
  }
type ATM = State ATS
--If the dead push 0 is repeated, the false sharing is not eliminated;
--TODO split each use of a small constant into a separate op to enable better
--codegen. Alt: let the code generator handle it.
allocTrivialAlgo :: Value ->
                    --liveness of param positions; includes jump/i dest,cond
                    ([Bool],[Bool]) -> 
                    ATM Value
allocTrivialAlgo (ws,ss) (live_ws,live_ss) = do
  ws' <- allocLoop ws live_ws
  ss' <- allocLoop ss live_ss
  return (ws',ss')
    where
      allocLoop :: [Var] -> [Bool] -> ATM [Var]
      allocLoop vs live_vs =
        forM (zip vs live_vs) $
        \(v,live) -> do
          if live
            then return v
            else do
            opMap <- gets atsOpMap
            if isTrivial opMap v
              then do
              encounterLHS $ trivialLHS v
              return v
              else allocTrivial v
      push0 = Push $ Serialized 0 0 []
--Replace v with v', emit v' = trivial op, add v' to scope.
allocTrivial :: Var -> ATM Var
allocTrivial v = do
  let op = trivialOp v
  v' <- allocVar v
  let lhs = trivialLHS v'
  encounterLHS lhs
  modify (\ats->ats{
             atsOpMap = M.insert v' (lhs, (op, ([],[]))) $
                     atsOpMap ats
             })
  return v'
encounterLHS :: Value -> ATM ()
encounterLHS lhs =
  modify (\ats->ats{atsEncountered = S.insert lhs $
                     atsEncountered ats})
trivialLHS v =
  if M.member (typeOfVar v) stateT2mnem
  then ([],[v])
  else ([v],[])
--One function for both stack and state vars
trivialOp v =
  case M.lookup (typeOfVar v) stateT2mnem of
    Just nm -> Op $ "empty" ++ nm
    --It must be a stack var:
    Nothing -> push0
--There's a conflict between consistent naming schemes (reducing bug
--risk) and IR readability here... perhaps change to first three letters.
stateT2mnem = M.fromList [
        (MemoryState,"Mem")
        ,(StorageState,"Sto")
        ,(TStorageState,"TSto")
        ,(CalldataState,"CD")
        ,(ReturndataState,"RD")
        ,(ExtStateState,"Ext")
        ,(OtherState,"Other")
        ]
push0 :: PrimOp
push0 = Push $ Serialized 0 0 []
--Does not check the lhs of the op, but there can only be one valid one for
--an op that returns one var of a given kind (stack or state).
isTrivial :: Map Var (Value,OpE) -> Var -> Bool
isTrivial opMap v =
  case M.lookup v opMap of
    --It's fine if a var is unbound; that means it's in the lhs (assuming the
    --Core is well-formed). An lhs var cannot be assumed to be trivial.
    Just (_lhs,(op,([],[]))) ->
      op == trivialOp v
    _ -> False
--Allocs a new var not currently in scope, with a related name to its
--predecessor for explanatory purposes.
allocVar :: Var -> ATM Var
allocVar v = do
  scope <- gets atsScope
  let (nm,scope') = runState (allocName $ nameOfVar v) scope
  modify (\ats->ats{atsScope=scope'})
  return v{nameOfVar = nm}

--Constant expansion (BB-local):
--Treat a var as constant if 1) it's a word param from lhs and its abstract
--value is exactly n or label lt lab, or 2) it's from a push.
--Propagation of sers could be part of symbolic opt (also BB-local).
--Rewrites with op tree depth > 1 are fine then, but whether they can be
--applied depends on whether the tree crosses a BB boundary.
--Fortunately, inlining merges BBs.

--Eta reduction:
--If f lhs = let x = g in jump g lhs, then f ~ g and f can be removed.
--Infinite loops have been eliminated, so removing f is now safe.
--Restrict to intraprocedural jumps to avoid confusing AI.
etaReduction :: OptRule
etaReduction ms core =
  let fdefs = M.toList $ coreDefuns core
      --For each eta-reducible f, the g it directly reduces to 
      f2g_ = M.fromList [(f,g) | (f,def) <- fdefs, Just g <- [etaCallee f def]]
      --But of course it must be normalized! If f eta-> g eta-> h, substituting
      --using f2g_ and deleting [f, g] will lead to f being replaced with g,
      --which no longer exists.
      f2g = normalizeEtaMap f2g_
      --Substitute all mentions of f for g in:
      --pushes (Serialized)
      --else branches (FunVar)
      --code global initializers (Serialized)
      --JTs (FunVar)
      --delete all fs
      --If there are no eta-reducible fs, do nothing.
  in --error $ "Eta-reducible: " ++ show f2g
    return $ if M.null f2g
             then core
             else Core {
    coreDefuns = M.map (substEtaDefun f2g) $
                 flip M.withoutKeys (M.keysSet f2g) $
                 coreDefuns core,
    coreStatic = M.map (substEtaSer f2g) $ coreStatic core,
    coreJTs = M.map (substEtaJT f2g) $ coreJTs core
    }
  where
    --Eta-reducible form:
    --ops = {gv = push g}
    --bv = (ws,mstk,ss)
    --branch = Jump ipc (gv:ws,mstk,ss)
    --That could be made less restrictive by requiring only that abvar(gv)=g,
    --but op DCE and constant expansion should simplify that to reducible form.
    --pruneDeadOps complicates this: dead branch params are bound to trivial
    --ops, meaning the body will no longer be just {gv = push g}.
    --However, since those params are dead they can be replaced with anything
    --to make the eta-reducible pattern fit.
    --Amended condition: if the only live op is gv = push g and
    --each var in the branch params either matches the lhs or is dead, f
    --is eta-reducible to g.
    etaCallee :: FunVar -> (BranchValue,OptFunRHS) -> Maybe FunVar
    etaCallee f (bv,(ops,branch)) =
      case branch of
        Jump Intraprocedural bv' ->
          let Just fi = M.lookup f $ funInfo ms
              IsFun {fiVars = v2av,
                     fiOpsLive = fiol
                    } = fiBodyInfo fi
              liveOps = M.filter (\(val,_) ->
                                    case M.lookup val fiol of
                                      Just (Id live) -> live
                                      _ -> error "!?") ops
          in case () of
               _ | M.size liveOps == 1,
                   --Could be a let but the Emacs Hs mode indenter
                   --doesn't like that
                   [(gv,push_g)] <- M.toList liveOps,
                   (_,(Push Serialized{serLength=2,
                                       serSizeof=2,
                                       serContent=[Right (0,2,g)]
                                      },_)
                   ) <- push_g,
                   M.member g $ coreDefuns core ->
                     --let (ws,mstk,ss) = bv
                     --in if bv' == (gv:ws,mstk,ss)
                     if etaMatches gv v2av bv bv'
                     then Just g
                     else Nothing
                 | let -> Nothing
        _ -> Nothing
    etaMatches gv v2av bv bv'
      | (ws,mstk,ss) <- bv,
        (dest:ws',mstk',ss') <- bv',
        length ws == length ws',
        length ss == length ss',
        mstk == mstk',
        dest == gv =
          --Each branch param var must either be equal to the corresponding
          --lhs var or be dead.
          let match lhsV argV =
                (lhsV == argV) || not (live argV)
              live v =
                case M.lookup v v2av of
                  Nothing -> error "!?"
                  Just av -> unId $ avLive av
          in and $ zipWith match (ws++ss) (ws'++ss')
      | let = False
         
--Pushes and jumpi else branches need substitution
substEtaDefun f2g (bv,(ops,branch)) =
  (bv,(M.map (substEtaPush f2g) ops, substEtaBranch f2g branch))
--Problem with op map repr: ops with multiple returned vars will be
--traversed repeatedly, which is asking for inconsistencies to arise.
substEtaPush f2g (lhs, (Push ser, ([],[]))) =
  (lhs, (Push $ substEtaSer f2g ser, ([],[])))
substEtaPush _ op = op
substEtaSer f2g ser = ser{
  serContent = map (\case Right (off,len,lab)
                            | Just g <- M.lookup lab f2g ->
                                Right (off,len,g)
                          x -> x) $ serContent ser
  }
substEtaBranch f2g = \case
  Jumpi else_f bv
    | Just g <- M.lookup else_f f2g -> Jumpi g bv
  branch -> branch
substEtaJT f2g (ar,fs) =
  (ar, map (\f ->
               case M.lookup f f2g of
                 Just g -> g
                 Nothing -> f) fs
  )
--Deja vu... need a graph algo module
--Given an acyclic map of direct eta reductions f->g, follows each f to its
--ultimate non-reducible destination.
--IOW, m[f] = g <=> f -> g
--For all f1->f2->...->fN st fN is not reducible, normalizeEtaMap m[f1]=fN.
{-
Algo:
out = {}
for f in keys m:
 follow f
follow f =
 if f in out:
  return out[f]
 if f in m:
  ult = follow m[f]
  out[f] = ult
  return ult
 return f
-}
normalizeEtaMap :: Ord k => Map k k -> Map k k
normalizeEtaMap m = execState (mapM_ (follow m) $ M.keys m) M.empty
  where
    follow :: Ord k => Map k k -> k -> State (Map k k) k
    follow m f = do
      mg <- gets $ M.lookup f
      case mg of
        --Already explored
        Just g -> return g
        Nothing ->
          case M.lookup f m of
            --Recurse and set f
            Just g -> do
              ult <- follow m g
              modify (M.insert f ult)
              return ult
            --Irreducible
            Nothing -> return f

--Inlining: to start with, inline only IP jumps where the dest has one
--predecessor (so there's no code size cost to inlining) and small (<=20 op)
--straight-line functions. Always inline if straight-line and #preds=1.
--TODO opt: identify chains of IP-inlinable BBs, inline the start of the
--chain and delete the rest. For now I'll just inline one at a time and leave
--it to iteration to get the same result.
  
--Intraprocedural inlining:
--f lhs = let ops in jump g args where g is a static fun and
--g lhs' = let ops' in branch =>
--f lhs = let ops;ops' in branch, where ops' and branch have been renamed to
--avoid clashes with ops.
--Inline iff g has only one pred, f.

--Straight-line function inlining:
--f lhs = let ops in call g,args,ret,scope
--g lhs' = let ops' in return $ret, val =>
--f lhs = let ops;ops' in jump intraprocedural ret,val,scope
--That's enough for primfuns and would already make a big difference.

--Inlines IP jumps with one pred and small straight-line calls. Proper inlining
--heuristics would require computing an exec intensity map and perhaps peeking
--BB => bytecode compilation, but this'll do for now since it covers primfuns.
--Finally code using words, primops etc will generate readable output...
--Algo:
--Identify functions which jump to a static dest.
--For each such f:
-- if mode = 1 and size target.preds == 1: inline
-- if mode = calling{} and target returns or exits: inline
--inline handles both call and IP jumps; if it's a call return is converted to
--a jump.
inlining :: OptRule
inlining ms core =
  return core{
  coreDefuns =
      --Using intersectionWith opt:
      --Note funInfo's keys are a superset of coreDefuns
      M.intersectionWith
      (\fi fundef@(flhs,(ops,branch)) ->
          case branch of
            Jump mode (dest:rest,_,ss) ->
              let v2av = fiVars $ fiBodyInfo fi
                  Just av = M.lookup dest v2av
              in case unlabel $ unId $ avVal av of
                   --f makes a static jump to g
                   --If it's a call, require g is a single-BB C fun
                   --If it's IP, require g has #preds=1
                   Just (Fun,g) ->
                     let Just fundef' = M.lookup g $ coreDefuns core
                     in if acceptable mode fundef' g ms
                        then inline fundef fundef'
                        else fundef
                   _ -> fundef
            _ -> fundef
      ) (funInfo ms) $ coreDefuns core
  }
  where
    --Given caller jump mode (Calling or IP), returns whether the callee
    --is inlinable.
    acceptable :: Mode -> Fundef -> FunVar -> FrozenModState -> Bool
    --ops must be of size <= 20 and have returning or exiting branch
    --Note M.size gives you the number of vars bound, not number of ops that
    --bind vars.
    acceptable Calling{} (_,(ops,branch)) _g _ms =
      let sz = S.size $ S.fromList $ M.elems $ M.map fst ops
          okBranch = case branch of
                       Jump Returning _ -> True
                       Jump {} -> False
                       Jumpi {} -> False
                       _ -> True
      in sz <= ipInliningSizeParam && okBranch
    --Must have #preds = 1
    acceptable Intraprocedural _fundef g ms =
      let Just fi = M.lookup g $ funInfo ms
      in M.size (unId $ preds fi) == 1
    --No other jump types may be inlined for now
    acceptable _ _ _ _ = False
--TODO collect config params into one place, perhaps allow them to be passed
--as compiler flags.
ipInliningSizeParam = 100

type Fundef = (BranchValue,OptFunRHS)
--Precondition: the first fundef is a jump to the second; the mode is either
--call or IP and if call then the second is a single-BB C function.
--NOTE: assumes no state var pruning for now.
--Algo: start by associating callee lhs vars with caller passed.
--For each lhs = op args in opsF, substitute args and lhs, allocating a new
--name if a var isn't present in the subst table.
--Substitute vars in the branch using the accumulated substitution table.
--In both call and IP, params need to be passed to the dest.
-- In call, they're the first arglen+1 words of the jump params + ss.
--  Need to change return in callee to IP; append scope unchanged.
-- In IP, they're unchanged.
inline :: Fundef -> Fundef -> Fundef
inline (lhs,
        (ops,
         Jump mode (dest:rest,_mstk,ss)))
  ((wsF,_,ssF),(opsF,branchF)) =
  let (gparams,adjustBranch) =
        case mode of
          Intraprocedural -> (rest,id)
          Calling (arglen,_retlen) ->
            let args_ret = take (arglen+1) rest
                scope = drop (arglen+1) rest
            in (args_ret,
                \branch ->
                  case branch of
                    --Set mode to IP if returning, add scope unchanged
                    Jump Returning (ret_val,mstk,ss) ->
                      Jump Intraprocedural (ret_val++scope,mstk,ss)
                    _ -> branch
               )
  in if length ss /= length ssF
     then error $ "Looks like you've pruned state vars; fix inline!"
     else let
    (lhsws,_,lhsss) = lhs
    initS = (S.fromList $ map nameOfVar $ lhsws ++ lhsss ++ M.keys ops
            , M.fromList $ zip (wsF++ssF) (gparams++ss)
            )
    (v_ops',(_,finalSubst)) = runState (mapM go $ M.toList opsF) initS
    ops' = M.union ops $ M.fromList v_ops'
    branch' = adjustBranch $ substBranch finalSubst branchF
    in (lhs,(ops',branch'))
  where go (v,(lhs,opE)) =
          (,) <$> substVar v <*> ((,) <$> substValue lhs <*> substOpE opE)
        --Avoids substituting the $stk var; TODO revisit when stk is actually
        --used.
        substBranch v2v =
          let subst v =
                case M.lookup v v2v of
                  Nothing -> error "!?"
                  Just v' -> v'
              substV (ws,ss) = (map subst ws, map subst ss)
              substBV (ws,mstk,ss) = (map subst ws, mstk, map subst ss) 
          in \case
            Jump mode bv -> Jump mode $ substBV bv
            Jumpi elf bv -> Jumpi elf $ substBV bv
            Revert v -> Revert $ substV v
            Return v -> Return $ substV v
            Stop v -> Stop $ substV v
--Invariant: the Set String is the set of live names so far in the post-inline
--def.
type InlineM = State (Set String, Map Var Var)
substVar :: Var -> InlineM Var
substVar v = do
  (scope,v2v) <- get
  case M.lookup v v2v of
    Just v' -> return v'
    Nothing -> do
      let (nm',scope') = runState (allocName $ nameOfVar v) scope
          v' = v{nameOfVar = nm'}
      put (scope',M.insert v v' v2v)
      return v'
substValue :: Value -> InlineM Value
substValue (ws,ss) = (,) <$> mapM substVar ws <*> mapM substVar ss
substOpE :: OpE -> InlineM OpE
substOpE (op,rhs) = (,) op <$> substValue rhs

--Symbolic simplification and constant expansion:
--Need a DSL for expressing symbolic rewrites such as x*a + y*b => x*(a+b)
--if x == y.
--For now, I'll limit symsimpl to ops in a single BB.
--But first, CE: if a var x used in an op has a small constant value k (a single
--label or 4-byte number), replace it with x' = push k.
--That'll eliminate arith on known values (esp. useful in deep stacks of
--functions) and deaden ops where the result value is known.
--Note I add pushes on use by ops, not branches; that avoids N pushes each BB
--for constant params. Replacement with pushes should deaden the params,
--ultimately allowing them to be eliminated via pruneParams.
--That should deal with the issue that f(x) pushes f first, then x, then
--needs to swap them to make the call.
--Note: sometimes it would be more efficient to remove a constant param from
--the stack, pushing it only when you jump to a BB in which it's not constant.
--TODO use FrozenModState during codegen: pushing instead of duping would be
--useful when the param is out of reach.
--TODO change the opmap repr to be in DB normal form; I waste code and cycles
--every time I need to do something once per op.
constantExpansion :: OptRule
constantExpansion ms core =
  return core{
  coreDefuns = M.intersectionWith
    (\fi (lhs@(ws,_,ss),(ops,branch)) ->
       let v2abv = M.map (unId . avVal) $ fiVars $ fiBodyInfo fi
           --Collect a map of small constants (<=4B)
           --Note it may include state vars, so need to be careful to only
           --alloc push ops for uses in the word part of op rhses.
           --To avoid an infinite loop where pushes are replaced with new
           --pushes, need to filter out the vs that are already pushes.
           v2k = M.filterWithKey
             (\v k ->
                 serLength k <= 4 &&
                 case M.lookup v ops of
                   Just (_,(Push _, _)) -> False
                   _ -> True) $
             M.mapMaybe abv2ser v2abv
           --For each v = k, map v to a new v' and its k
           v2v'k = evalState (sequence $ M.mapWithKey
                               (\v k -> (,) <$> allocVar v <*> return k) v2k) $
                   S.fromList $ map nameOfVar $ ws ++ ss ++ M.keys v2k
           --for each v -> lhs=op (ws,ss) in ops:
           -- for each w in ws:
           --  if (v',k) = v2v'k[w]:
           --   add v'->v'=push k to newOps
           --   replace w with v'
           --To CE non-push ops with constant results passed to branch params:
           --for each w in ws of branch:
           -- if (v',k) = v2v'k[w] && ops[w] is non-push:
           --  add v' to newOps, replace w with v' (TODO)
           ((ops',branch'),newOps) = flip runState M.empty $ do
             ops' <- go v2v'k ops
             branch' <- substBranch v2v'k ops branch
             return (ops',branch')
       in (lhs,(M.union ops' newOps,branch'))
    )
    (funInfo ms) $ coreDefuns core
  }
  where
    --Accepts labels and integer constants; TODO extend AbVar to support
    --Serialized directly.
    abv2ser :: AbVar -> Maybe Serialized
    abv2ser abv
      | Just (_lt,lab) <- unlabel abv =
          Just $ Serialized 2 2 [Right (0,2,lab)]
      | Just n <- unexactly abv = Just $ serWord n
      | let = Nothing
    allocVar :: Var -> State (Set String) Var
    allocVar v = do
      nm' <- allocName $ nameOfVar v
      return v{nameOfVar = nm'}
    go v2v'k ops =
      forM ops (\(lhs,(primOp,(ws,ss))) -> do
                   ws' <- mapM (allocAndSubst v2v'k) ws
                   return (lhs,(primOp,(ws',ss))))
    allocAndSubst :: Map Var (Var,Serialized) -> Var ->
                     State OpMap Var
    allocAndSubst v2v'k v =
      case M.lookup v v2v'k of
        Nothing -> return v
        Just (v',k) -> do
          modify $ M.insert v' (([v'],[]), (Push k,([],[])))
          return v'
    substBranch :: Map Var (Var,Serialized) -> OpMap -> Branch ->
      State OpMap Branch
    substBranch v2v'k ops =
      let substBV (ws,mstk,ss) = do
            ws' <- mapM substParam ws
            return (ws',mstk,ss)
          substV (ws,ss) = (,) <$> mapM substParam ws <*> return ss
          --If v is in ops, then allocAndSubst; that checks whether
          --it's also in v2v'k, implying it's a small constant and not a
          --push.
          substParam v =
            if M.member v ops
            then allocAndSubst v2v'k v
            else return v
      in \case
        Jump mode bv -> Jump mode <$> substBV bv
        Jumpi elf bv -> Jumpi elf <$> substBV bv
        Revert v -> Revert <$> substV v
        Return v -> Return <$> substV v
        Stop v -> Stop <$> substV v

--TODO make a convenient API for adding new ops; I've duplicated use of
--allocName in several places.


--Step 1: prune unreachable functions.
--Inlining may restrict abvars, which restricts control flow.
--It's therefore not possible to prune unreachable functions, JTs or codeGs
--just once... it must be done on every iteration!
--Better apply as many rewrites as possible each iteration then.

--Use AI and per-BB symbolic reasoning to apply opts
--TODO log opt rules applied.
--Top prio:
-- *********************************DCE****************************************
--Prune unreachable funs.
--Replace any mentions of unreachable funs with 0x01.
--Prune static data whose codeGs are never dereferenced; I can check that by
--looking at the from abvar of each codecopy op.
--Replace any mentions of undereferenced codeGs with 0x01.
--Eliminate dead ops unless they're 0 and only passed to dead params;
--replace dead params with 0.

--If ret is dead in a C function due to constant return address, for each call
--to it with dead ret, change the mode to CallingFixedReturn (args,ret) cont
--and don't pass ret. Eliminate $ret from the function.
--Such jumps should continue to the given cont.

--If ret is dead in a C function due to guaranteed exit, elim $ret from its
--args; for each call to such functions, drop ret and the remaining scope.
--Set mstk to Nothing.
--If a BB may not exit (directly or indirectly), then it diverges:
--replace it with
--f _ = let z = push 0
--          m = emptyMem
--revert(z,z,m).
--Then earlier BBs covered by the same rule will be able to exit! That's fine,
--their vars will be dead and it will be possible to inline them to revert.
--However, they should all be substituted in one pass.
--TODO add mayExit to AI, but not mayReturn.

--Partition BBs into calling conventions (sources,dests).
--If f -> g, they must be in the same CC with f in sources, g in dests.
--Dropping or reordering of params must be done to a whole CC at a time; a
--dropped position must be dead for every g in dests.

-- ***************************Constant expansion*******************************

--If a var is a small constant (k or label), push it; that interacts with
--DCE and needs to be done after constant-ret function transformation if
--applied to ret.

-- ******************************Inlining**************************************

--A jump is a candidate for inlining iff its dest is a constant label.
--I don't yet handle inlining jumpis.
--Heuristic: if a BB has only one pred, inline it if possible.
--Riskier heuristic: if a C function is a single BB that returns or exits
--and its size is <= k, inline it if possible. That covers primfuns.
--Then inlining the jump ret is optional; if not inlined it must be converted
--to IP.

--Simple size estimate: total size of ops + total number of word args
--The size of a push is 1 + the size of its immediate argument.
--Note the estimate isn't perfect, since it doesn't consider whether or how
--many stack shuffling instructions are necessary.
--The branch should also be included.
--It should be possible to get the upper bound using the swap bound on
--permutations (2n+1?).

--Intraprocedural jumps are simple to inline: rename the vars in the dest,
--union source ops with dest ops and replace the source branch with the dest
--branch.
--Call jumps that aren't fully inlined need to move the inter-function
--boundary: pass the scope, then replace IP jump with call and return with
--IP. How to deal with that for jumpi? Might need to add mode.

--TODO track SCCs of C functions; loops make naively inlining small BBs
--dangerous. Note BBs should be inlined in topological order:
--if f -> g -> h, inlining f->g only to inline f->h again later is wasted work.
--Note specialization via copying BBs or whole SCCs is worth *trying* in case
--it enables further optimizations - ideally it should be possible to
--backtrack!

--Inlining is guaranteed to reduce jumps iff you inline the straight-line
--skeleton.
--Ex: a and b jump to f, which falls through to g.
--If a inlines f but not g, then the jump is only delayed.
--Choose fallthrough in opt? That would benefit from exec intensity calculation.
--Would that be convenient to calculate incrementally alongside AI
--(changing as the graph grows)? Would need to look at the equations.
--Aside: AI could assist in branch probability estimation.
--If the loop counter is [1..100] and the branch cond is == 100, the probability
--can be estimated to be some function of 1%.
--On inlining loops: the straight-line skeleton of a while loop is <= the
--cond and body.

-- *****************************Eta reduction**********************************

--If f args = jump g args, every mention of f can be replaced with g.
--Problem: need to preserve the call boundary. For the entrypoints to C
--functions (which are always eta-reducible), that's not a problem.
--If h -> f was ipc and f -> g a call, then h -> g needs to become a call.
--Why is that? To preserve continues dataflow.
--f may be pushed far away from its use, but if so it's a C function.
--What if $trueMain is eta-reducible? I could add an entrypoint field... for
--now just don't eta reduce it.

--Related: duplicate codeGs could be merged. That's weaker than using overlap,
--which should be done during codegen.
--Equal or overlapping JTs could be merged!

-- ************************Symbolic simplification*****************************

--AI can recognize abvar + 0 = abvar, but that just says the result has the
--same set of possible values as the left summand - not that they're identical.
--SymSimp can go further by applying rewrite rules:
--x+0 = x --eliminates an add
--f & 0xff = f
--Commuting and grouping constants: x+1+2 => 3+x
--Distribution: 12x + 4y = 4(3x + y) using GCD. That can eliminate a mul if
--two or more summands share a factor. It could also be used to replace MUL
--with the cheaper SHL.

--Idea: an equation DSL that handles applying the rules.
--DAGs to DAGs?
--e1<x>, e2<x>, x = k => e1<x1>, x1 = k, e2<x2>, x2 = k --replicates work,
--but eliminates a false dependency.
--A DAG of lets
--(tup) = tree<vars>; ...
--is the same repr as that used for treegraph scheduling!
--But treegraph is not necessarily optimal for the EVM due to nonempty
--initial stack, multi-word target stack, 0 or 1 returns, and state deps.
