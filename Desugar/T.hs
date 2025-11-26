{-# LANGUAGE LambdaCase #-}
module Desugar.T (desugarT) where

--To separate out desugaring of datatypes, desugarT must be moved lower.

import Desugar.DTs
import qualified E.Abs as P
import qualified DeclBucket
import AST.Util

import Data.Generics (everything,mkQ,everywhere,mkT)

--TODO propagate loc info
desugarT :: DeclBucket.T -> T
desugarT = struct2append . go
  where go = \case
          P.TVar _loc (Ident nm) -> TyVar nm
          P.TNat _loc n -> TyNat n
          P.TCon _loc(UIdent nm) -> TyCon nm
          P.TEmptyTup _loc -> TyCon "Unit"
          P.TTup _loc t ts -> tupleT $ map go $ t:ts
          P.TApp _loc tf tx -> go tf :$$ go tx
          P.TArray _loc len a -> Array (go len) (go a)
          P.TArrow _loc a b -> go a :-> go b
--Desugars Struct a b c to Append a (Append b (Append c Unit))
struct2append :: T -> T
struct2append = everywhere $ mkT $
  \case t | (TyCon "Struct", ts) <- rollTyApps t ->
            foldr (\a b -> TyCon "Append" :$$ a :$$ b) (TyCon "Unit") ts
          | let -> t
