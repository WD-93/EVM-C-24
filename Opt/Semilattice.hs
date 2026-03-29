module Opt.Semilattice where

import Data.Set (Set(..))
import qualified Data.Set as S

--I don't need the whole semilattice package...
class JoinSemilattice a where
  (\/) :: a -> a -> a
--Require semilattice instance? Problem: a may have either join or meet.
class HasBottom a where
  bottom :: a
class HasTop a where
  top :: a

instance JoinSemilattice Bool where
  (\/) = (||)
instance HasBottom Bool where
  bottom = False
instance HasTop Bool where
  top = True

instance Ord a => JoinSemilattice (Set a) where
  (\/) = S.union
instance HasBottom (Set a) where
  bottom = S.empty
--Set is finite, so it does not in general have a top. It would in principle
--be possible to define top for e.g. Int, but it would be impractical.

--Might need instances for Maybe, Map later.
instance JoinSemilattice a => JoinSemilattice (Maybe a) where
  Nothing \/ x = x
  x \/ Nothing = x
  Just a \/ Just b = Just $ a \/ b
