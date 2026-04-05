module Opt.AI.EVM (opBehavior) where

import Opt.Semilattice
import Opt.AbVar

import Data.Map (Map(..))
import qualified Data.Map as M

--Defines the abstract behavior of straight-line Core ops, i.e. the
--non-branching EVM ops less DUP*, SWAP*, POP.

type OpFun = AbValue -> AbValue
type AbValue = ([AbVar],[AbVar])
opBehavior :: Map String ((Int,Int), --arg arity
                          (Int,Int), --ret arity
                          OpFun --behavior
                         )
opBehavior = M.fromList [
  
                        ]
