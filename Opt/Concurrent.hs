{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies, LambdaCase #-}
module Opt.Concurrent where

import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad
import Data.Kind (Type(..))

--Experimenting with the AI = increasing vars linked by circuits triggered
--by updates idea.

--Poorer man's concurrency transformer: just need spawn, no yield
--TODO add a prio param?
class Monad m => Concurrent m where
  spawn :: m () -> m ()
  scheduler :: m ()
newtype ConcT m a = ConcT {runConcT :: StateT [ConcT m ()] m a}
  deriving (Functor,Monad,Applicative)
instance Monad m => Concurrent (ConcT m) where
  spawn m = ConcT $ modify (m:)
  scheduler = go
    where go = ConcT get >>= \case
            [] -> return ()
            ms -> ConcT (put []) >> sequence_ ms >> go
--Q: Is FIFO more efficient? LIFO would trigger op updates immediately, even
--when other vars would be updated.

--Mutable vars that notify consumers on update.
data MutVar m a = MutVar {mvState :: Ref m a,
                          mvConsumers :: Ref m [a -> m ()]
                         }
--Constraint: the Ref type family is parameterized by m, so
--m may have only one ref type instead of refs having one monad.
--Using a class is nicer than having a Ref datatype which contains its own
--methods, since class methods are statically known and can be inlined.
class Monad m => HasRef m where
  type Ref m :: Type -> Type
  newRef :: a -> m (Ref m a)
  readRef :: Ref m a -> m a
  writeRef :: Ref m a -> a -> m ()

readMutVar :: HasRef m => MutVar m a -> m a
readMutVar = readRef . mvState
writeMutVar :: (Concurrent m, HasRef m, Eq a) => MutVar m a -> a -> m ()
writeMutVar mv new = do
  let ref = mvState mv
  old <- readRef ref
  if old /= new
    then do
    fs <- readRef $ mvConsumers mv
    sequence_ [spawn (f new) | f <- fs]
    writeRef ref new
    else return ()
modifyMutVar :: (Concurrent m, HasRef m, Eq a) =>
  (a -> a) -> MutVar m a -> m ()
modifyMutVar f mv = do
  a <- readMutVar mv
  writeMutVar mv $ f a
--Subscribe to updates of a MutVar
subMutVar :: HasRef m => MutVar m a -> (a -> m ()) -> m ()
subMutVar mv f = do
  let ref = mvConsumers mv
  fs <- readRef ref
  writeRef ref (f:fs)

--Circuit patterns:
--With increasing ops and out = fold op ins where op is monotonic and
--idempotent, new in vars can be added incrementally as ins grows.
--Each in is linked to out by in changed => out op= in. I'll call that
--link (|=).
--Ex applicable ops: (||) for reachability, (&&) for inevitability,
--least upper bound of AbVars.
(|=) :: (Concurrent m, HasRef m, Eq a) =>
  MutVar m a -> (a -> a -> a, MutVar m a) -> m ()
outv |= (op,inv) = do
  --Postcondition: outv >= inv
  --First outv op= inv to ensure it holds even before inv is next updated
  a <- readMutVar inv
  modifyMutVar (op a) outv
  subMutVar inv (\a -> modifyMutVar (op a) outv)
--For all elements in a growing set, some equation applies.
--First apply it to each existing element, then to new ones as they're
--added. The callback uses an additional ref to track deltas.
--Ex use:
--Core: bb lhs = let ops in call v,args,ret,scope
--for all f in funs(v):
-- f.args |= args
-- if f may return, ret.scope |= scope
forAll :: (Concurrent m, HasRef m, Ord a) =>
  MutVar m (Set a) -> (a -> m ()) -> m ()
forAll set property = do
  as <- readMutVar set
  forM_ (S.toList as) property
  subDelta set as S.difference (mapM_ property)
subDelta :: HasRef m => MutVar m a -> a -> (a -> a -> b) -> (b -> m ()) -> m ()
subDelta mv init diff callback = do
  tracker <- newRef init
  subMutVar mv (\new -> do
                   old <- readRef tracker
                   writeRef tracker new
                   callback $ diff new old)
--TODO ensure a is ascending by using Ord? It might be nontrivial to verify,
--even if the overall program can be proven to increase the mv.
