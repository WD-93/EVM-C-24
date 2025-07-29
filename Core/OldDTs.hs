module Core.DTs where

import AST.DTs (Name(),T())

import Data.Generics

--Simplification: Core can be mononomorphic!
--Core names can be either Name or (Name,[T]) (indicating type application);
--no need for mangling.
data CName = Simple Name | TyApplied Name [T]
  deriving (Eq,Ord,Show,Data)

--EVMC Core is a functional IR to which the EVMC Module AST is compiled.
--As in GHC, modules are compiled to a single Core letrec expression.
--Because EVMC control flow includes non-local jumps (break,continue,return in
--statements, stop() et al in expressions), EVMC functions are converted to
--CPS where the last argument is a continuation.
--Calls are represented as f args (\ret -> ...).
--Side-effecting exprs are represented by passing and returning state values:
--mem, calldata etc.
--Globals and static values are represented as pointers which are initially
--in scope... alongside a state map for their initial values?
--Put them in a letrec?
--Control flow constructs:
--ifte cond f1 f2 args
-- | cond = f1 args
-- | let  = f2 args
--Ifte must take two functions without closed because neither can be a
--continuation.
--case tag sharedArgs conts
--Branching/divergent primitives
--All functions take a single argument, a tuple.

--Design goals:
--Allow interprocedural inlining, specialization (e.g. removal
--of unused arguments).
--Tail call optimization
--Constant expansion and sharing
--Reordering of independent function calls (FW)
--A fine-grained memory model and anti-aliasing rules, symbolic eval involving
--memory (FW)
--Mem repr: a non-overlapping set of ranges (index,bytestring).
--Nondeterministic semantics: at any time a GC step which modifies mem map
--and pointers reachable from stack/globals but preserves observational
--equivalence of reads and writes may be applied.
--Obs eq is only guaranteed if you avoid UB (saturating mem space, setting
--pointers to arbitrary values) or dependence on byte values of pointers.
--Ex opt justified by mem model: bounded-size malloc of pointer dropped on
--return => use fixed scratch memory instead (useful for code and returndata
--deref, sha3).

--Compilable form:
--Primfun applications lifted to lets
--Only vars in expressions, no expr nesting except for structs; letrec function
--instantiation via let.
--All lambdas except those in cont position lifted to letrec
--contE ::= ifte | case | contPrim | funCall
--funCall may have a lambda of the form (\e -> f e args) as its last argument,
--where f e args is another funCall.
--That's because f args is represented as f, arg1, arg2, ... on the stack.
--(\e -> f e args) is represented as f,args on stack.
--Because continuations are in general of unknown stack length, they must be
--last (BoS).

--Compiling patterns:
--Simple patterns are of two types: pointer or stack. Pointer patterns
--translate into a *ptr, where fields and indexing become functions applied to
--the ptr.
--(*p).field = e => writePtr (ptrField p) e
--sv.field = e => let sv' = setField e sv
--Con args is more complex... its args may be both pointer and stack.
--If the datatype has multiple constructors, first case.
--Boxed dt: deref tag, case on it, coerce ptr to associated struct unboxed dt,
--arg pats = deref.

data Core = CInteger Integer
          | CVar CName      --including primfuns, globals and static?
          | App Core Core
          | Let Name Core Core
          | Letrec (Map CName Core) Core
  deriving (Eq,Ord,Read,Show,Data)
