{-# LANGUAGE LambdaCase #-}
module Opt.AI.EVM (opBehavior,pushBehavior) where

import Opt.Semilattice
import Opt.AbVar
import Const.Const (Serialized(..))

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
--Push isn't part of the opBehavior map, but it makes sense to define its
--interpretation here.
--Given a map label => lt and a Serialized, returns the abstract value of
--Push ser. Uses a function rather than a Map to avoid having to M.union
--every time a push is interpreted.
--If ser is a single right-aligned label lab of len 2, look up its type and
--return {lt: {lab}}
--If ser is only bytes, returns {possKs = n}
--Otherwise, returns an abvar containing all mentioned labels with possKs = All.
--Errors with Left lab at the first unrecognized label lab.
pushBehavior :: (String -> Maybe LabelType) -> Serialized -> Either String AbVar
pushBehavior lab2lt Serialized{serContent = sc}
  | [Right (0,2,lab)] <- sc = mkLabel lab 
  | all (\case Left _ -> True
               _ -> False) sc = do
      let bs = do Left bs <- sc
                  bs
      return bottom{possKs = K $ sum $ zipWith (*) (iterate (*256) 1) $
                             map fromIntegral $ reverse bs
                   }
  | let = do
          labvars <- mapM mkLabel [lab | Right (_,_,lab) <- sc]
          return (foldr (\/) bottom labvars){possKs = All}
          where mkLabel lab = label <$> classify lab <*> return lab
                classify lab =
                  case lab2lt lab of
                    Nothing -> Left lab
                    Just lt -> return lt
