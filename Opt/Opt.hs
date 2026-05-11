{-# LANGUAGE LambdaCase, PatternSynonyms,
 StandaloneDeriving, TypeSynonymInstances, FlexibleInstances, DeriveDataTypeable
#-}
module Opt.Opt where

import Core.RestrictedCore
import Opt.AI
import Core.SSA (OptCore(),OptFunRHS())
import Util ((?))
import Const.Const
import Opt.HTraversable (Id(..))
import Opt.Analysis.Exitness (Exitness(..),analyzeExitness)
import Core.PrimTypes (pattern W)
import AST.DTs (pattern Memory, pattern UInt)

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Generics
import Control.Monad.State

--Opt errors are compiler errors
data OptError = OptAIError AIError
  deriving (Eq,Ord,Read,Show)
--I'll need to repeatedly run ai.
opt :: OptCore -> Either OptError OptCore
opt = iteratively optimize

--Apply transformation until error or convergence
iteratively :: Eq a => (a -> Either err a) -> a -> Either err a
iteratively f = go
  where go a = do
          a' <- f a
          if a == a'
            then return a
            else go a'

--Problem: AI is expensive, so we want to perform it as rarely as possible.
--However, opt rules may invalidate the results.
--For now I'll redo AI whenever a rule fires rather than try to be clever.
optimize :: OptCore -> Either OptError OptCore
optimize core = do
  ms <- ai core ? OptAIError
  applyRules ms core [pruneUnreachableFuns
                      ,revertDivergent
                      ,etaReduction
                     ]
--Invariant: ms pertains to core
applyRules ms core =
  \case [] -> return core
        rule:rules -> do
          core' <- rule ms core
          if core == core'
            then applyRules ms core rules
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
substUnreachable :: Data a => Set FunVar -> a -> a
substUnreachable ur = everywhere (mkT go)
  where go :: Serialized -> Serialized
        go ser = ser{serContent = normalizeContent $
                      map (\case Right (off,len,lab)
                                   | (off,len) == (0,2) ->
                                     if S.member lab ur
                                     then Left [0,1]
                                     else Right (off,len,lab)
                                   | let -> error "!?"
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
--Ops: prune dead ops unless 0 and passed to dead params; if dead and passed
--to dead param replace with 0.

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
    etaCallee :: FunVar -> (BranchValue,OptFunRHS) -> Maybe FunVar
    etaCallee f (bv,(ops,branch)) =
      case branch of
        Jump Intraprocedural bv'
          | M.size ops == 1,
            --Could be a let but the Emacs Hs mode indenter doesn't like that
            [(gv,push_g)] <- M.toList ops,
            (_,(Push Serialized{serLength=2,
                               serSizeof=2,
                               serContent=[Right (0,2,g)]
                              },_)
            ) <- push_g,
            M.member g $ coreDefuns core ->
            let Just fi = M.lookup f $ funInfo ms
                IsFun {fiVars = v2av} = fiBodyInfo fi
                Just av = M.lookup gv v2av
                abv = unId $ avLive av
                (ws,mstk,ss) = bv
            in if bv' == (gv:ws,mstk,ss)
               then Just g
               else Nothing
        _ -> Nothing
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
