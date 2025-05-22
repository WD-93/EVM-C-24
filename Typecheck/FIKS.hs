{-# LANGUAGE OverloadedStrings, LambdaCase #-}
module TypeCheck.FIKS (fiks,FIKSError()) where

import AST.DTs
import Util (complainIf, (?))

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Except
import Data.List (elemIndex)
import Control.Arrow ((***))

--The second step of typechecking after tysyn subst; it's split out from the
--other stages to simplify them. After FIKS is done, kind check need only look
--up tycon kinds in one place.
--It must be done after tysyn subst because otherwise
--type T = Type
--D : T
--data D = {}
--would wrongly error with the complaint that D is not of kind Type.

fiks :: Module -> Either (Name,FIKSError) Module
fiks m = do
  let ksigs = kindsigs m
      dts = M.map fst $ datatypes m --we only care about params
      tycons = S.toList $ S.union (M.keysSet ksigs) (M.keysSet dts)
  tyconks <- mapM (\tycon -> do
                      kind <- handleTyCon tycon (M.lookup tycon ksigs)
                              (M.lookup tycon dts)
                              (M.lookup tycon $ datatypeRegions m) ?
                              ((,) tycon)
                      return (tycon,kind)) tycons
  return m{kindsigs = M.fromList tyconks}
data FIKSError = RegionParamNotPresent [Name] Name
               | ValueTyConMustReturnType T
               | KindSigArityAndDataArityMustMatch [T] [Name]
               | RegionParamHasWrongKind Name T
               | NonDataKindMayNotReturnType T
  deriving (Eq,Ord,Read,Show)
--Three cases:
--Tycon has both kind sig k and data decl Tycon args:
-- if Tycon has region param r:
--  require r is in args; let's say it's at position ix
--  require param ix of k is Region
-- require k returns Type
--Tycon has only data decl Tycon args:
-- if it has region param r:
--  require r is in args; let's say it's at position ix
--  kind = Type*|args| (with [ix] set to Region) -> Type
-- else kind = Type*|args| -> Type
--Tycon has only kind sig k:
-- require k does not return Type
handleTyCon :: Name -> (Maybe T) -> (Maybe [Name]) -> Maybe Name ->
  Either FIKSError T
handleTyCon tycon (Just k) (Just args) mr = do
  let (params,ret) = splitTyFun k
  complainIf (ret /= "Type")
    $ ValueTyConMustReturnType k
  complainIf (length params /= length args)
    $ KindSigArityAndDataArityMustMatch params args
  case mr of
    Just r -> do
      ix <- getRegionIx r args
      let rk = params !! ix
      complainIf (rk /= "Region")
        $ RegionParamHasWrongKind r rk
      return k
--A kind which just has a kind decl is syntactically guaranteed to not also
--have a region param
handleTyCon tycon (Just k) _ _ = do
  let (_,ret) = splitTyFun k
  complainIf (ret == "Type")
    $ NonDataKindMayNotReturnType k
  return k
handleTyCon tycon _ (Just args) mr = do
  let argKs = map (const "Type") args
  f <- case mr of
         Nothing -> return id
         Just r -> do
           ix <- getRegionIx r args
           return $ setAt ix "Region"
  return $ unSplitTyFun (f argKs,"Type")

--Splits a kind into its arguments and result.
--Example: splitTyFun (A -> B -> C) = ([A,B],C)
--Written verbosely because I got a weird type error... due to monomorphism
--restriction?
splitTyFun :: T -> ([T],T)
splitTyFun (a :-> b) =
  let (ts,t) = splitTyFun b
  in (a:ts,t)
splitTyFun t = ([],t)
--The inverse.
unSplitTyFun :: ([T],T) -> T
unSplitTyFun (ts,t) = foldr (:->) t ts
--Requires r is in args and returns its index
getRegionIx :: Name -> [Name] -> Either FIKSError Int
getRegionIx r args =
  case elemIndex r args of
    Just ix -> return ix
    Nothing -> throwError $ RegionParamNotPresent args r
--Sets the ix'th element of list as to a
--Partial: errors if the index is out of range
setAt :: Int -> a -> [a] -> [a]
setAt ix _ _ | ix < 0 = error "negative index"
setAt ix a as = go ix a as
  where go 0 a (_:as) = a:as
        go n a (a':as) = a':go (n-1) a as
        go _ _ _ = error "too high index"
