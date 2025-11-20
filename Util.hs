{-# LANGUAGE DeriveFunctor, LambdaCase #-}
module Util where

import Control.Monad.Except
import System.IO.Unsafe (unsafePerformIO)
import Data.Map (Map(..))
import qualified Data.Map as M
import GHC.Stack

--General utility functions that should be available to any module and don't
--fit anywhere else.

(?) :: Either localErr a -> (localErr -> globalErr) -> Either globalErr a
Right b ? _ = Right b
Left err ? errt = Left $ errt err


 
complainIf :: MonadError err m => Bool -> err -> m ()
complainIf b err
  | b = throwError err
  | let = return ()

debugFlag = True
--For debugging
unsafePrint :: Monad m => String -> m ()
unsafePrint str
  | debugFlag = unsafePerformIO $ putStrLn str >> return (return ())
  | let = return ()

--TODO remove this and replace uses with the lib-provided withError.
withError :: MonadError e m => (e -> e) -> m a -> m a
withError f action = catchError action (throwError . f)

--Turns out I need this in Desugar as well.
--Given a positive integer, returns the minimum number of bytes required to
--contain it. Treatment of negative numbers (e.g. using signextend to
--trade exec cost against code size) is left to codegen.
log256 :: Integer -> Int
log256 n | n < 0 = error $ "Negative argument to log256: " ++ show n
         | let = go n
                 where go 0 = 0
                       go n = succ $ go $ n `div` 256

--Using M.! anywhere was a mistake... I'll now replace it with this to get
--error location info.
(!) :: (HasCallStack, Show k, Show v, Ord k) => Map k v -> k -> v
m ! k =
  case M.lookup k m of
    Just v -> v
    Nothing -> error $ "Missing key in (!): " ++ show (k,m)

--I'm sure I have this somewhere... TODO find and deduplicate
count :: Ord a => [a] -> Map a Int
count = foldr (adjustWithDefault succ 0) M.empty

--Applies f to m[k], or inserts d if m doesn't have that mapping.
--Useful when you want to track info about keys, but the set of possible keys
--is unknown so you can't initialize the map in advance.
adjustWithDefault :: Ord k => (v -> v) -> v -> k -> Map k v -> Map k v
adjustWithDefault f d = M.alter (Just . maybe d f)

--The Errors applicative (it's not a monad) lets you report many errors at
--once from independent computations.
data Errors err a = Errors [err]
                  | Success a
  deriving (Eq,Ord,Read,Show,Functor)
instance Applicative (Errors err) where
  pure = Success
  --An IO-list could ensure accumulation is O(n) despite accumulation from the
  --left; TODO.
  Success f <*> Success x = Success $ f x
  Errors xs <*> Errors ys = Errors $ xs ++ ys
  Errors xs <*> _ = Errors xs
  _ <*> Errors xs = Errors xs
runErrors :: Errors err a -> Either [err] a
runErrors = \case
  Errors errs -> Left errs
  Success a -> Right a
fling :: err -> Errors err a
fling = Errors . (:[])
