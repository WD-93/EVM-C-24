module Monads where

import Data.Map (Map(..))

--The type to which all normal EVMC values are coerced to/from.
--The memory map is a partial map Integer -> Byte
type Bytestring = [Byte]
type Byte = Int
--The base monad, implements side effects and CALL-global divergence:
--revert and RETURN
data Result a = RETURN Bytestring
              | REVERT Bytestring
              | Return (a,[Log],S)
data Code a = Expr {runExpr :: (R,S) -> Result (a,[Log],S)}
data R = R {calldata :: Bytestring}
  deriving (Eq,Ord,Read,Show)
data S = S {memory :: Map Integer Byte --inefficient but it's a model...
           ,gas :: Integer
           }
  deriving (Eq,Ord,Read,Show)
data Log = Log [Topic] Bytestring
  deriving (Eq,Ord,Read,Show)
type Topic = Integer

data Cont s a where
  Break s :: s -> Cont s s
  Continue :: s -> Cont s s
  Value :: a -> Cont s a 
data WhileT s m a = WhileT {runWhileT :: m (Cont s a)}
while :: Monad m => (s -> m (Bool,s)) -> (s -> WhileT s m s) -> s -> m s
while cond body s = go s
  where go s = do
          (b,s') <- cond s
          cont <- runWhileT (body s')
          case cont of
            Break s -> return s
            Continue s -> go s
            Value s -> go s
break :: Monad m => s -> WhileT s m s
break s = WhileT $ return $ Break s
continue :: Monad m => s -> WhileT s m s
continue s = WhileT $ return $ Break s
liftWhile ma = WhileT $ Value <$> ma
