module Opt.AI where

import Opt.Concurrent
import Opt.AbVar
import Opt.Semilattice
import Core.RestrictedCore

import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Map (Map(..))
import qualified Data.Map as M

--The module that defines the EVMC program abstract state and its recursive
--equation.
--Because CB treats Chans as the unit of incremental computation and
--separates them from the monad for constructing circuits, the state and
--its recursive equation can be given a straightforward, readable definition.

--The module state in the solver context.
--I could param by wrapper (Chan s when solving, Id later), but let's not get
--too fancy.
data ModState s = MS {
  reachable :: Map FunVar (Chan s Bool)
                     }
--Basic blocks consist of a series of nested iftes terminated by a non-ifte.
--It can be divided into SLSes (straight-line sections) consisting of
--ops and a branch.
--Each SLS has its own LHS and liveness status for vars... a var that's live
--in the jumpi may become dead in the else branch.
--Perhaps it would be better to represent the static else branch as a FunVar
--rather than a nested FunRHS...
--Then I eliminate the difference between BBs and SLSes.
--However, I introduce the possibility of an else branch having multiple
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
