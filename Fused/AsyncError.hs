{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
FlexibleInstances, UndecidableInstances #-}
module Fused.AsyncError where

import Control.Monad.Except
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

--I currently have a mysterious "no instance for is_dynamic@[WordPad uint32]"
--in my EVMC Solidity ABI library, but Fused doesn't tell me where.
--I need to add context a la "In f1:t1, f2:t2, f3:t3 ... no instance for fN:tN".

--To give the context of error messages, I originally stacked on context using
--withError. However, Fused spawns asynchronous tasks, and later execution
--of a spawned task will not run with the context given by withError.
--I need to be able to extract and persist the context stack when spawning to
--get helpful error messages.
--I don't need to inspect the stack on its own, so it's fine for it to be a
--list of e -> e.

class Monad m => AsyncError e m | m -> e where
  --A variant of withError; I needn't convert every withError to stackError,
  --just the explores.
  stackError :: (e -> e) -> m a -> m a
  --When spawning a new task, need to extract the current stack and store it
  --with the task. Why ask? Because AsyncError is Reader-like: changes to the
  --stack only need to be local.
  askErrorStack :: m [e -> e]
  --When running the task, need to set the stack for the duration of the task.
  setErrorStack :: [e -> e] -> m a -> m a

newtype AsyncExcept e a = AE {
  unAE :: [e -> e] -> Either e a
  }
instance Functor (AsyncExcept e) where
  fmap f (AE g) = AE $ (f <$>) . g
--One should be able to derive Applicative from Monad... if instances defined
--a single record datatype they would be more composable.
--A more general underlying for instance: exists T where nm = e
instance Applicative (AsyncExcept e) where
  pure = AE . const . Right
  mf <*> mx = do
    f <- mf
    x <- mx
    return $ f x
instance Monad (AsyncExcept e) where
  return = pure
  AE g >>= f =
    AE $ \ctx ->
           case g ctx of
             Left e -> Left e
             Right a -> unAE (f a) ctx

instance MonadError e (AsyncExcept e) where
  --throwError takes the context stack and applies it to the error.
  throwError e = AE $ \ctx -> Left $ foldr (.) id (reverse ctx) e
  catchError (AE g) f =
    AE $ \ctx ->
           case g ctx of
             Left e -> unAE (f e) ctx
             Right a -> Right a

instance AsyncError e (AsyncExcept e) where
  stackError e2e (AE g) = AE $ g . (e2e:)
  askErrorStack = AE $ Right
  setErrorStack ctx (AE g) = AE $ g . const ctx

--This should be derivable... TODO something cleverer.
instance AsyncError e m => AsyncError e (ReaderT r m) where
  stackError e2e m = do
    r <- ask
    lift $ stackError e2e $ runReaderT m r
  askErrorStack = lift askErrorStack
  setErrorStack ctx m = do
    r <- ask
    lift $ setErrorStack ctx $ runReaderT m r
instance AsyncError e m => AsyncError e (StateT s m) where
  stackError e2e m = do
    s <- get
    (a,s') <- lift $ stackError e2e $ runStateT m s
    put s'
    return a
  askErrorStack = lift askErrorStack
  setErrorStack ctx m = do
    s <- get
    (a,s') <- lift $ setErrorStack ctx $ runStateT m s
    put s'
    return a
instance (Monoid w, AsyncError e m) => AsyncError e (WriterT w m) where
  stackError e2e m = do
    (a,w) <- lift $ stackError e2e $ runWriterT m
    tell w
    return a
  askErrorStack = lift askErrorStack
  setErrorStack ctx m = do
    (a,w) <- lift $ setErrorStack ctx $ runWriterT m
    tell w
    return a
