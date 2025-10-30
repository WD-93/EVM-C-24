{-# LANGUAGE PatternSynonyms #-}
module Core.PrimTypes where

import AST.DTs

--Core introduces a number of primitive types to be able to represent
--the lower-level implementation of EVMC; they're collected here for
--readability.
--Tycons are appended with # to ensure they can't be shadowed by C-level
--tycons.

--The type of Core functions; each basic block in C is converted into a
--Core function. In Core, the type of the entire stack being passed is
--explicit; that means functions must be polymorphic in stk.
--State variables (representing state which doesn't live on the stack such
--as memory, calldata etc) are also passed; that is intended to enable
--reasoning about side effects.
--New: I'll replace -># with Cont#.
--Cont : Type -> State -> Type
--jump : Arg (Cont a s * a) s -> End
--Consequence: Type can contain State
pattern Cont a s = TyCon "Cont#" :$$ a :$$ s
--(*) means Pair, but the problem with that is Pair : Type^2 -> Type doesn't
--enforce linked-list normal form as SPair does for SElems.
--Introduce a new Stack kind? Not for now.

--The stack is a single tuple of kind Type. State variables don't live on
--the stack and have no size; they're of kind SElem. Examples include
--MemSlice (representing a slice of memory) and Calldata.
--State is the kind of tuples of SElems.
--Side-effecting ops are represented as pure functions which consume and
--produce state.
--Because they must manipulate both stack values and state, all ops take and
--return an Arg : Type -> State -> Argument
--a are the dynamic values, s the state vars
pattern Arg a s = TyCon "Arg#" :$$ a :$$ s
--SPair : SElem -> State -> State 
pattern SPair selem st = TyCon "SPair#" :$$ selem :$$ st
--SUnit : State
pattern SUnit = TyCon "SUnit#"

--Arg lets you combine Type and State; SPair and SUnit let you combine
--multiple SElems. The SElems to be combined are listed below.

--MemSlice is the type of slices of memory; in future alloc will consume
--a splittable AllocPtr SElem and produce a new MemSlice.
--For now effects are limited to expressing whether an entire region was
--read/modified.
--Tracking effects is necessary for safely reordering or pruning ops; I aim to
--enable more flexible reordering with richer effects in future.
--Note MemSlice is distinct from Memory :: Region, a C-level parameter used to
--indicate pointer region without giving any clues as to *where* into memory
--it points.
pattern MemSlice = TyCon "MemSlice#"
--Calldata is immutable, so there's no reason to slice it.
--It can't just be called Calldata because the name's taken by the Region.
pattern CalldataState = TyCon "CalldataState#"

--SElem /= Type, so you need separate tuple constructors
sTupleT :: [T] -> T
sTupleT [] = SUnit
sTupleT (t:ts) = SPair t (sTupleT ts)
