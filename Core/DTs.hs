{-# LANGUAGE OverloadedStrings, DeriveDataTypeable #-}
module Core.DTs where

import AST.DTs
import Data.Generics

--Monomorphized EVMC modules are converted to a single pure Core expression,
--taking a S# (the EVM state type).
--All variables are tagged with type; there are only monomorphic functions.
--f : a -> b => f :: (a,S#) -> Return# (b,S#).
--Use Append instead of tuple?
--Core need not be aware of value representation; Core primitives such as
--Return# a and Memory lack a straightforward bytestring repr.
--Bytestring# is a variable-size value without a size tag; it has meaning only
--in the language semantics, not in the compiled code.
--Ex: data Return# a = ... | RETURN Bytestring#
--Bytestring# values can be coerced:
--getMem off len mem :: Bytestring#
--derefToStack#@[Memory,a] (MkPtr off) mem =
-- coerce# (getMem off (sizeof@a P@a) mem)

--Global pointers can be passed as parameters; they're assumed to be disjoint

data Expr = Var Id T
          | Lit Integer --a word
          | Arr [Expr]  --Novel; the Array constructor would be variadic
          | App Expr Expr
          | Lam Id Expr
          | Let Id Expr Expr
          | Case Expr [(P,Expr)]
          --Omitted: Coercion
  deriving (Eq,Ord,Read,Show,Data)

data Id = Mono Name | Poly (Name,[T])
  deriving (Eq,Ord,Read,Show,Data)
--Multi-level inspection enabled for infallible patterns (e.g. Append a b)
--Wild has been eliminated; use a fresh name for ignored fields
data P = PVar Id T | PCon Id [P]
  deriving (Eq,Ord,Read,Show,Data)
evmState :: T
evmState =
  structT [extState,
           memory,
           storage,
           tstorage,
           calldata,
           returndata,
           code
          ]
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
