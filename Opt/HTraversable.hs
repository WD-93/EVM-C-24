{-# LANGUAGE RankNTypes, KindSignatures #-}
module Opt.HTraversable where

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Kind (Type(..))

--Overloading the circuit combinators to strip out incrementality for testing
--requires HTraversable, formerly defined in Opt.AI, to be used in Concurrent.
--I'm therefore splitting it out into its own module.
--The state -> upd -> m () callbacks in forAll and forAllMap felt ugly...
--to make the code extensible I must now uncover the beautiful underlying
--structure.
class HTraversable t where
  htraverse :: Applicative f =>
    (forall a . g a -> f (h a)) -> t g -> f (t h)

--Id also belongs here, since it's the identity type that remains after
--mutability has been removed from a structure parameterized by Chan s.
--There's an analogy between running monads to remove effects and removing
--impurity from data structures in monads.
newtype Id a = Id {unId :: a}
  deriving (Eq,Ord,Read,Show)
instance Functor Id where
  fmap f = Id . f . unId
instance Applicative Id where
  pure = Id
  Id f <*> Id x = Id $ f x
instance Monad Id where
  return = pure
  Id a >>= f = f a
--Freezing can be implemented for multiple instances of Circuit, but the type
--to be frozen by htraversal needs to be a barbie type that specifies how
--its components are to be recursed on.
--Map k doesn't give enough information: you might want to stop at map,
--traverse n layers deep etc.
--Solution: a stack analogous to monad transformers, terminated by Id1
--(analogous to the Identity monad).
--Each foldSet and foldMap accumulator needs a barbie type.

--The base element of the barbie transformer stack, named Id1
--because it's like an identity on the 1-arity type constructor f (if you
--swapped the argument order).
newtype Id1 a f = Id1 {unId1 :: f a}
instance HTraversable (Id1 a) where
  htraverse f (Id1 x) = Id1 <$> f x
--Convention: BT means Barbie Transformer
--The t param specifies how to htraverse the nested structure.
newtype MapBT k t (f :: Type -> Type) = MapBT (Map k (t f))
instance HTraversable t => HTraversable (MapBT k t) where
  htraverse f (MapBT m) = MapBT <$> traverse (htraverse f) m
newtype ListBT t (f :: Type -> Type) = ListBT [t f]
instance HTraversable t => HTraversable (ListBT t) where
  htraverse f (ListBT tfs) = ListBT <$> traverse (htraverse f) tfs
newtype PairBT t1 t2 (f :: Type -> Type) = PairBT (t1 f, t2 f)
instance (HTraversable t1, HTraversable t2) => HTraversable (PairBT t1 t2) where
  htraverse f (PairBT (a,b)) =
    PairBT <$> ((,) <$> htraverse f a <*> htraverse f b)
