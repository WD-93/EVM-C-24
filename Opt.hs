module Opt where

import Core.RestrictedCore

--The optimizer for Core; transforms a Core module into a (hopefully) more
--efficient one.
--First step: SSA, convert op sequence to DAG.
--Flagship opts: DVE, inlining, TCO, DCE, sym eval
--Old opts:
--dead var/op elimination. Generalization: do so across loops.
--Inlining. Bypassing empty blocks is an instance of that.
--New:
--symbolic eval (k1 + k2 = k3, x+0 = x etc)
--By using abstract interpretation I could establish approximate info about
--values, e.g. bounds and slice symbolic value.
--Ex use: x % 32 = x iff 0 <= x < 32.
--Distribute %k across summands, elim zeroes.
--Replace mul, div, mod 2^n with shl, shr, and
--Sym eval repeated construct/dot operations (shift, mask, or)
--If a var is only used as a jumpi cond opts which only preserve truthy
--can be applied.
--DCE: convert jumpi with cond of known truthiness to a jump.
--Mem opt: dropping writes just before a stop() should be possible.
--FW: sym eval of memory; aggregation of overlapping loads, elim of overwritten
--writes.
--FW: Separate disjoint mem slices, enabling reordering.
--FW: Reorder branches to speed up the most likely (or optimistic) path.
-- That requires swapping jumpi funRHSes with the true-cond rhs.
