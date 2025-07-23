{-# LANGUAGE LambdaCase #-}
module AST.Util where

import Data.Set (Set(..))
import qualified Data.Set as S

import AST.DTs

--Utility functions for manipulating AST DTs; TODO deduplicate

--Given an application f x y ... z, returns (f,[x..z])
rollApps :: E -> (E,[E])
rollApps = roll (\case f :$ x -> Just (f,x)
                       _ -> Nothing)
unrollApps :: E -> [E] -> E
unrollApps = foldl (:$)

rollTyApps :: T -> (T,[T])
rollTyApps = roll (\case f :$$ x -> Just (f,x)
                         _ -> Nothing)
unrollTyApps :: T -> [T] -> T
unrollTyApps = foldl (:$$)

--Generic roll and unroll
--roll collects repeated application arguments into a list; unroll is its
--inverse.
roll :: (a -> Maybe (a,b)) -> a -> (a,[b])
roll sel a =
  let (f,rargs) = go a []
  in (f,reverse rargs)
  where go a rbs =
          case sel a of
            Just (a',b) -> go a' (b:rbs)
            Nothing -> (a,rbs)
--Generic unroll is just foldl

--The free vars (all of which should be locals in scope) of a pattern.
--Free vars in subexprs such as in *e are not included.
--Therefore naive everything won't work.
freeVarsPat :: Pat -> Set Name
freeVarsPat = go
  where go = \case
          PWild -> S.empty
          PVar nm -> S.singleton nm
          Deref _ _ -> S.empty
          PDot _ p _ -> go p
          PBang _ p _ -> go p
          PConArgs _ _ ps -> S.unions $ map go ps
          PCon _ _ nmps -> S.unions $ map (go . snd) nmps

--The function name to which each constructor of Op corresponds
op2fun :: Op -> Name
op2fun = \case
  Plus -> "plus"
  Minus -> "minus"
  Mul -> "multiply"
  Div -> "divide"
  Mod -> "modulo"
  Shl -> "shL"
  Shr -> "shR"
  And -> "bwAnd"
  Or -> "bwOr"
  Xor -> "bwXor"
