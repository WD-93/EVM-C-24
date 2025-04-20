module Desugar where
--A separate module for desugaring; Compiler should just tie each stage
--together and handle the IO.

{-
import E.Par (pM,myLexer)
import E.ErrM (Err(..))
import E.Abs (Ident(..),UIdent(..),Infix(..),OS(..))
import qualified E.Abs as P
-}

--CST -> AST
import DTs
import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.Trans.Except
import Control.Monad.State
import Text.Read (readMaybe)
import Data.List (sort)
