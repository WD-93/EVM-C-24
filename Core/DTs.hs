{-# LANGUAGE OverloadedStrings, DeriveDataTypeable, PatternSynonyms #-}
module Core.DTs where

import AST.DTs
import Data.Generics
import Data.Map (Map(..))

--Monomorphized EVMC modules are converted to a single pure Core expression,
--taking a Env (the EVM state type).
--All variables are tagged with type; there are only monomorphic functions.
--f : a -> b => f : ((a,Cont b),Env) -> End
--type Cont b = (b,Env) -> End
--type Env = <evmState>
--data End = Return (Bytestring,...) | Revert Bytestring

--Core need not be aware of value representation; Core primitives such as
--Memory lack a straightforward bytestring repr.
--Bytestring# is a variable-size value without a size tag; it has meaning only
--in the language semantics, not in the compiled code.
--Bytestring# values can be coerced:
--getMem off len mem :: Bytestring#
--deref#@[Memory,a] (MkPtr off) mem =
-- coerce# (getMem off (sizeof#@a P@a) mem)

{-
Core program structure:
 \(cd,ap) ->
  let g1..gn = alloc --global allocation
      c1..cn = alloc --code pointer allocation?
      code = c1->v1 ||| ...
  in letrec fs = ...
     --initial value assignment?
  in main (((),\_ -> stop#),env)
-}
--Full env: the 6 regions, misc BC state, gas

data Expr = Var Id
          | PrimFun Name [T] --A primfun may only occur fully applied
          | Lit Integer --a word
          | Arr [Expr]  --Novel; the Array constructor would be variadic
          | App Expr Expr
          | Lam P Expr
          | Letrec [(Id,Expr)] Expr --for def of mutually recursive constants
          | Let P Expr Expr --for dynamic binding
          --caseTag t {Nil: \((xs,scope),env) -> ...}
          | CaseTag Expr (Map Name Expr)
          --Adding Pair and Unit as constructors avoids tagging them with
          --redundant types; the type can be inferred from the arguments.
          | EPair Expr Expr
          | EUnit
          -- | Case Expr [(P,Expr)]
          --Omitted: Coercion
          --Every continuation returns End, so I don't need polymorphism
          {-
          --I need QP for converting EVMC to a CPS monad, but I only need it
          --for that... so I'll implement it as a type lambda.
          | TyLam Name Expr
          | TyApp Expr T
          --TyApp (TyLam v e) t ~ substitute (TyVar v) for t in e until it's
          --shadowed.
          -}
  deriving (Eq,Ord,Read,Show,Data)

data Id = Mono Name T | Poly (Name,[T]) T
  deriving (Eq,Ord,Read,Show,Data)
--x | tup are the only allowable Core patterns because they allow for zero-cost
--deconstruction; the rest are implemented using case and field access.
--Problem: Wild is currently converted to a new local in C, but there's no
--corresponding local declaration.
data P = PVar Id | PUnit | PPair P P
  deriving (Eq,Ord,Read,Show,Data)
--The type of the env threaded state monad-style through Core expressions.
evmState :: T
evmState =
  tupleT evmStateTs
evmStateTs :: [T]
evmStateTs =
  [extState,
   memory,
   storage,
   tstorage,
   calldata,
   returndata,
   code
   --To add: log, gas, allocPtr, misc BC state
  ]
--The default pattern used for the env in every Core function.
--Must be a proper tuple to match evmState
env :: P
env = tuplePCore $ zipWith (\t nm -> Core.DTs.PVar $ Mono nm t) evmStateTs $
  words "$ext $mem $sto $tst $cd $rd $co"

tuplePCore :: [P] -> P
tuplePCore = foldr PPair PUnit

--For now, just regions and ExtState#
extState :: T
extState = "ExtState#"
memory :: T
memory = "Memory#"
storage :: T
storage = "Storage#"
tstorage :: T
tstorage = "TStorage#"
--Calldata is immutable; data Calldata# = Calldata# Bytestring#
calldata :: T
calldata = "Calldata#"
--Returndata is mutable; while you can't mutate it directly you can set a
--new returndata using *CALL or CREATE*
returndata :: T
returndata = "Returndata#"
--Code is immutable, but since the addressable data is not at a fixed offset
--(and data not containing PUSH* may be interleaved with bytecode) it must
--be a partial map like Memory# et al.
code :: T
code = "Code#"

--Additional Core types:
--The type of pure bytestrings; every user type has a fixed-length
--bytestring repr.
bytestring :: T
bytestring = "Bytestring#"
--The final result type of a contract CALL:
--data End# = Return# (Bytestring#,Storage#,ExtState#,...)
--          | Revert# Bytestring#
end :: T
end = "End#"
--Core functions; toFun#[a,b] and fromFun#[a,b] convert between a -> b and
--((a,(b,evmState) -># End#),evmState) -># End.
pattern a :-># b = "->#" :$$ a :$$ b
