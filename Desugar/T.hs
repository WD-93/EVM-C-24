{-# LANGUAGE LambdaCase #-}
module Desugar.T (desugarT) where

--To separate out desugaring of datatypes, desugarT must be moved lower.

import Desugar.DTs
import qualified E.Abs as P
import AST.Util

import Data.Generics (everything,mkQ,everywhere,mkT)

desugarT :: P.T -> T
desugarT = struct2append . go
  where go = \case
          P.TVar (Ident nm) -> TyVar nm
          P.TNat n -> TyNat n
          P.TCon (UIdent nm) -> TyCon nm
          P.TEmptyTup -> TyCon "Unit"
          P.TTup t ts -> tupleT $ map go $ t:ts
          P.TApp tf tx -> go tf :$$ go tx
          P.TArray len a -> Array (go len) (go a)
          P.TArrow a b -> go a :-> go b
--Desugars Struct a b c to Append a (Append b (Append c Unit))
struct2append :: T -> T
struct2append = everywhere $ mkT $
  \case t | (TyCon "Struct", ts) <- rollTyApps t ->
            foldr (\a b -> TyCon "Append" :$$ a :$$ b) (TyCon "Unit") ts
          | let -> t
