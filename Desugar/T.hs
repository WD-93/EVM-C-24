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
desugarT = go
  where go = \case
          P.TVar _loc (Ident nm) -> TyVar nm
          P.TNat _loc n -> TyNat n
          P.TCon _loc(UIdent nm) -> TyCon nm
          P.TEmptyTup _loc -> TyCon "Unit"
          P.TApp _loc1 (P.TCon _loc2 (UIdent "Struct")) tup
            | Just ts <-
              case tup of
                P.TEmptyTup _ -> Just []
                P.TTup _ t ts -> Just $ t:ts
                _ -> Nothing ->
              foldr (\a b -> TyCon "Append" :$$ a :$$ b) (TyCon "Unit") $
              map go ts
          P.TTup _loc t ts -> tupleT $ map go $ t:ts
          P.TApp _loc tf tx -> go tf :$$ go tx
          P.TArray _loc len a -> Array (go len) (go a)
          P.TArrow _loc a b -> go a :-> go b
--Bugfix and syntax change: previously I intended to use Struct a b c as the
--syntax for struct types, but naively using everywhere for that leads to
--Struct a b c desugaring to () a b c.
--Fix: change struct type syntax to Struct (a,b,c), consistent with struct
--expr and pattern syntax.
{-
--Desugars Struct a b c to Append a (Append b (Append c Unit))
struct2append :: T -> T
struct2append = everywhere $ mkT $
  \case t | (TyCon "Struct", ts) <- rollTyApps t ->
            foldr (\a b -> TyCon "Append" :$$ a :$$ b) (TyCon "Unit") ts
          | let -> t
-}
