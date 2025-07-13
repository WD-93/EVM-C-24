{-# LANGUAGE LambdaCase #-}
module AST.Util where

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
