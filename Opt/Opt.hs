module Opt.Opt where

--Before this'll work properly, need to set and loopback the state vars
--in $trueMain. Loopback requires identifying non-revert exiting branches
--and feeding their sto and tsto to $trueMain.

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
--Problem: need to preserve the call boundary.
--If h -> f was ipc and f -> g a call, then h -> g needs to become a call.
--Why is that? To preserve continues dataflow.
--f may be pushed far away from its use, but if so it's a C function.

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
