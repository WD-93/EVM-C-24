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

--TODO update transformers/mtl and fix dependencies in cabal...
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
