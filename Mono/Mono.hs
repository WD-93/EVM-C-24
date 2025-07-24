module Mono.Mono where

--On the EVM, you can't afford boxing datatypes by default.
--EVMC therefore has a Hindley-Milner type system with template polymorphism,
--in contrast to Haskell's approach of passing boxed class dicts.
--That allows id : a -> a to work for both Word and (Word,Word); separate
--machine code is generated for each instance.
--To achieve that, EVMC modules must first be monomorphized: starting from
--main : () -> (), type annotations containing rigid tyvars are replaced with
--monomorphic types. For each f @ monoTs, a new monomorphic function is
--allocated.
--For class functions, an instance must be selected first.
--This phase also tree-shakes the relevant function instances and globals.
--Note that globals are already monomorphic... but they must still be explored
--to get the full function instance set.

import AST.DTs

--Algo:
--First look up main;
--unify its type with () -> (), obtaining the params ts to pass to its scheme
--monoFun f monoTs:
--If f@monoTs has not yet been created:
-- Look up f's scheme, replace scheme's vars with monoTs in its body
-- Wherever a f@polyTs is encountered,
--  updTs = update polyTs using the var=>monoT mapping
--  monoFun f updTs
--  replace with f@updTs
-- funs[f@monoTs] = the updated definition
--If Con@monoTs has not yet been explored:
-- Explore from its monomorphized tag.

--When monomorphizing a class function, also need to instantiate.
--That's never relevant to tag expressions, which should be static.

--There are three dynamic-relevant fields:
--defuns, globals, dtsInfo.
--Root: main
--Funs can mention funs, globals and constructors
--Globals and tag expressions contain static exprs; those may in turn refer
--to all three.
