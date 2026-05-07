{-# LANGUAGE LambdaCase,
 StandaloneDeriving, TypeSynonymInstances, FlexibleInstances, DeriveDataTypeable
#-}
module Opt.Opt where

import Core.RestrictedCore
import Opt.AI
import Core.SSA (OptCore())
import Util ((?))
import Const.Const
import Opt.HTraversable (Id(..))

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Generics

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
  applyRules ms core [pruneUnreachableFuns]
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
