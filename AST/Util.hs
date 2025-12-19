{-# LANGUAGE LambdaCase #-}
module AST.Util where

import AST.DTs

import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Generics

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
roll sel a = go [] a
  where go rbs a =
          case sel a of
            Just (a',b) -> go (b:rbs) a'
            Nothing -> (a, rbs)
--Generic unroll is just foldl

--The free vars (all of which should be locals in scope) of a pattern.
--Free vars in subexprs such as in *e are not included.
--Therefore naive everything won't work.
freeVarsPatG :: (a -> a -> a) -> (Maybe T -> Name -> a) -> a -> Pat -> a
freeVarsPatG f2 f1 f0 = go
  where go = \case
          PWild _ -> f0
          TypedPVar mt nm -> f1 mt nm
          Deref _ _ -> f0
          PDot _ p _ -> go p
          PBang _ p _ -> go p
          PCon _ _ nmps -> foldr f2 f0 $ map (go . snd) nmps
freeVarsPat :: Pat -> Set Name
freeVarsPat = freeVarsPatG (S.union) (const S.singleton) S.empty
freeVarsPatList :: Pat -> [Name]
freeVarsPatList = freeVarsPatG (++) (const (:[])) []
--Used in compiling the pattern matching of the lhs in Fused.
--Errors if any PVar isn't typed.
freeTypedVarsPatList :: Pat -> [(Name,T)]
freeTypedVarsPatList = freeVarsPatG (++)
  (\mt nm ->
      case mt of
        Nothing -> error "Compiler error: untyped PVar after HM"
        Just t -> [(nm,t)]) []

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

region2T :: Region -> T
region2T = TyCon . (\case
                       Me -> "Memory"
                       St -> "Storage"
                       TS -> "TStorage"
                       Ca -> "Calldata"
                       Re -> "Returndata"
                       Co -> "Code")

--Gathers all mentioned tyvars and returns them in order of first mention
--Moved from Typecheck.HM
tyVarsList :: T -> [Name]
tyVarsList = fst . tyVarsListSet
tyVarsListSet :: T -> ([Name],Set Name)
tyVarsListSet = everything (\(nms1,snms1) (nms2,snms2) ->
                              (nms1 ++ filter (not . flip S.member snms1) nms2,
                               S.union snms1 snms2)) $ mkQ ([],S.empty) $
                \case TyVar nm -> ([nm],S.singleton nm)
                      _ -> ([],S.empty)

--The default (vars,t) pair for a scheme; if f : a -> b then its scheme will
--be ([a,b],a -> b)
mkSig :: T -> ([Name],T)
mkSig t = (tyVarsList t, t)

--Returns whether a kind is concrete (ultimately returns a Type); used in
--Desugar.
kindIsConcrete :: T -> Bool
kindIsConcrete = (== TyCon "Type") . snd. rollFunApps

--t1 -> t2 ... -> t<n> -> ret => n
typeArity = length . fst . rollFunApps

--TODO deduplicate
--a -> b -> c -> d => ([a,b,c],d)
rollFunApps :: T -> ([T],T)
rollFunApps = go
  where go = \case
          a :-> b ->
            let (ts,ret) = go b
            in (a:ts,ret)
          t -> ([],t)
unrollFunApps :: ([T],T) -> T
unrollFunApps (ts,ret) = foldr (:->) ret ts
