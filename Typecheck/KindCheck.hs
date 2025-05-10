{-# LANGUAGE OverloadedStrings, LambdaCase #-}
module TypeCheck.KindCheck (kindCheck,KindCheckError(..)) where

import Util
import AST.DTs

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Generics

data KindCheckError = UnderappliedArrow
                    | TyNameNotInScope Name
                    | BadTyApp T T T T
                    | ShouldBeType T
                    | In String Name KindCheckError
  deriving (Eq,Ord,Read,Show)

--The universe of kinds is defined in AST.DTs:
--Int :: Signedness -> Nat -> Type
--Ptr :: Region -> Type -> Type
--value types :: Type
--Signed, Unsigned :: Signedness
--the regions :: Region
--Datatypes: Type* -> Region -> Type
--Enums: Type
--Type, a -> b :: Type (this isn't Agda...)
getKindMap :: Module -> Map Name T
getKindMap m =
  --Datatype kind is currently fixed by arity
  let dtkinds = M.map (\(args,_) ->
                         foldl  (\t _ -> "Type" :-> t)
                         ("Region" :-> "Type") $ init args) $ datatypes m
      enumkinds = M.map (const "Type") $ enums m
  in M.unions [dtkinds,enumkinds,primTyConKinds]

--defuns: tysigs and all types in exprs must be Type
--static: all types must be type
--datatypes: all types must be type
kindCheck :: Module -> Either KindCheckError ()
kindCheck m = do
  let kinds = getKindMap m
  --I remove the globals to avoid an erroneous complaint that their regions
  --aren't types:
  --Aha, tysyns need to be emptied as well; tysyn bodies may contain any
  --kind.
  let m' = m{globals = [], tysyns = M.empty}
  checkTopLevelTypes kinds m'
  --Now to check the globals
  mapM_ (\(nm,_region,t) -> wellkinded kinds t ? In "global" nm) $ globals m
--Generic programming: I want to check every top-level type (but not their
--subcomponents) are well-kinded Types.
--The only exception is global region, which must be Region (but that's
--syntactically guaranteed).
checkTopLevelTypes :: Data a => Map Name T -> a -> Either KindCheckError ()
checkTopLevelTypes kinds =
  mapM_ (wellkinded kinds) . topLevelTypes
topLevelTypes :: Data a => a -> [T]
topLevelTypes = everythingBut (++) (mkQ ([],False) ty)
  where ty :: T -> ([T],Bool)
        ty t = ([t],True)

kind :: Map Name T -> T -> Either KindCheckError T
kind kinds = go
  where go = \case
          a :-> b -> do
            go a; go b
            return "Type"
          TyCon "->" -> Left UnderappliedArrow --can't determine kind
          t | Just nm <- name t ->
              case M.lookup nm kinds of
                Just k -> return k
                Nothing -> Left $ TyNameNotInScope nm
          tf :$$ tx -> do
            kf <- go tf
            kx <- go tx
            case kf of
              a :-> b
                | a == kx -> return b
              _ -> Left $ BadTyApp tf kf tx kx
          TyNat _ -> return "Nat"
          Struct fields -> do
            let subts = map (\(_,_,t) -> t) fields
            mapM_ (wellkinded kinds) subts
            return "Type"
        name = \case
          TyCon nm -> Just nm
          TyVar nm -> Just nm
          _ -> Nothing
--Checks kind and requires the given type :: Type; used extensively in the
--main module check (where every top-level type but global regions must be
--a Type).
wellkinded :: Map Name T -> T -> Either KindCheckError ()
wellkinded kinds t = do
  k <- kind kinds t
  complainIf (k /= "Type") (ShouldBeType k)
