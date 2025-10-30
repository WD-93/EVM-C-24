{-# LANGUAGE LambdaCase #-}
module Sizeof where

import AST.DTs
import AST.Util (rollTyApps)
import Mono.Mono (instT) --TODO move to AST.Util

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

--Simply computes the size of every mentioned monotype, failing if there's
--a cycle where A contains B contains C ... contains A.
--More detailed info such as field offset is computed from DTsInfo and size
--info. Array, Int and Pair are treated specially and are not cached.
type Size = Integer
type MonoT = (Name,[T]) --A monomorphic type of form TyCon ts
type Sizeof = Map MonoT Size
type SizeofError = [MonoT] --A cycle
computeSizeof :: DTsInfo E -> --Info about all DTs, includes placeholders 4 prim
                 Set MonoT ->
                 Either SizeofError Sizeof
computeSizeof dtsi tyconTs =
  runExcept $
  flip execStateT M.empty $
  flip runReaderT dtsi $
  mapM_ sizeofM $ S.toList tyconTs

type SizeM = ReaderT (DTsInfo E) (StateT (Map MonoT Size) (Except SizeofError))
--Go takes a set argument for efficient error detection and a list for
--error reporting.
sizeofM :: MonoT -> SizeM Size
sizeofM = go [] S.empty
  where
    go :: [MonoT] -> Set MonoT -> MonoT -> SizeM Size
    go stk set = memoize
      (\case
          ("Array",[TyNat len, a]) ->
            (len *) <$>  goWithT stk set a
          ("Int",[_s, TyNat len]) ->
            return len
          ("Pair",[a,b]) -> do
            sza <- goWithT stk set a
            szb <- goWithT stk set b
            return $ sum $ map (`roundedUpMod` 32) [sza,szb]
          --tycon is a datatype which follows the default
          --rules.
          (tycon,ts) -> do
            --First look up DTInfo
            dtsi <- ask
            case M.lookup tycon $ datatypes dtsi of
              Nothing -> error $
                "Compiler error: tycon " ++ tycon ++ " out of scope in sizeofM"
              Just dti ->
                if dtBoxed dti
                then return 2 --It's just a wrapped pointer
                else do
                  --Repr = tag ++ (union of (concat of each con's args))
                  let cons = dtCanonicalCons dti
                      params = dtParams dti
                      --Now we must instantiate the DT's argument types
                      param2t = M.fromList (zip params ts)
                      argss :: [[T]]
                      argss = map (\con ->
                                     case M.lookup con (conInfo dtsi) of
                                       Nothing ->
                                         error $
                                         "Compiler error: no coninfo for " ++
                                         "canonical con " ++ con ++ " of " ++
                                         tycon
                                       Just ci ->
                                         map (\(_,t) ->
                                                case instT param2t t of
                                                  Left nm -> error "?!?"
                                                  Right t' -> t'
                                             ) $
                                         conFields ci
                                  ) cons
                  tagSz <- case dtTagScheme dti of
                             Nil -> return 0
                             N16 -> return 1
                             N1 n -> return $ fromIntegral n
                             Custom tagT _ -> goWithT stk set tagT
                  argsSizes <- mapM 
                               ((sum <$>) . mapM (goWithT stk set)) argss
                  return $ tagSz + maximum argsSizes
      )
    goWith :: [MonoT] -> Set MonoT -> MonoT -> SizeM Size
    goWith stk set p =
      if S.member p set
      then throwError $ reverse (p:stk)
      else go (p:stk) (S.insert p set) p
    goWithT :: [MonoT] -> Set MonoT -> T -> SizeM Size
    goWithT stk set t =
      case rollTyApps t of
        (TyCon tycon, ts) -> goWith stk set (tycon,ts)
        other -> error $ "Compiler error: ill-kinded type slipped through: "
                 ++ show t
    memoize :: (MonoT -> SizeM Size) -> MonoT -> SizeM Size
    memoize handler k = do
      mv <- gets $ M.lookup k
      case mv of
        Nothing -> do
          v <- handler k
          modify (M.insert k v)
          return v
        Just v -> return v
