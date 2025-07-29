module Core.Core where

import qualified AST.DTs as E --as in EVMC
import Core.DTs
import Mono.Mono (MonoS(..))

--Converts a monomorphized EVMC module to a Core lambda
core :: (Module,MonoS) -> Either CoreError Expr
core = error "todo"

--The ways Core conversion can go wrong
data CoreError = BreakOutsideLoop
               | ContinueOutsideLoop
  deriving (Eq,Ord,Read,Show)

--Program expr parameters: each global, s#
--Globals include <r>allocPtr
--mallocPtr is stored in memory

--A statement is well-behaved iff it contains no non-local control flow:
--break or continue.
--Halting exprs are OK; a well-behaved while becomes
--(scope',s') <- f (scope,s)
--The same is true for ifte.
--break => Return# (scope',s'), continue => f (scope',s'),
--where f is the last enclosing while loop and scope' fits it.
{-Ex where scope is different in different loops:
var x = 10;
while (x--) {
 var y = 10;
 while (y--) x--;
}
--Break and continue necessitate CoreError, since occurring outside a loop is
--malformed.

--Every subexpr becomes
--x <- e
--Add a Bind constructor to speed up rewrites?
--Return# a >>= f = f a
--Revert# bs >>= _ = Revert# bs --etc

--Now EVMC primfuns must be given explicit definitions in terms of Core
--primfuns.
--They're computed from the given type params; a failing lookup shouldn't
--always throw an error, as dynamically sized values (FW) lack a sizeof but
--can support dynSizeof.
-- *dsp1 = *dsp2 can use dynSizeof instead of sizeof.

--times a b has a different shape depending on signedness;
--FW: incrementally move such overloading to Prim.evmc
