module Util where

import Control.Monad.Except
import System.IO.Unsafe (unsafePerformIO)

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
