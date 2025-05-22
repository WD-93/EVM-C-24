{-# LANGUAGE OverloadedStrings, LambdaCase #-}
module TypeCheck.KindCheck (kindCheck,KindCheckError(..)) where

import Util
import AST.DTs

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Generics

--Update: datatypes now have an optional kind signature.
--Iterate over tycons in keys kindsigs U keys datatypes, looking at whether
--each tycon has a kindsig and datatype def respectively.
--Unboxed datatypes (those with no entry in datatypeRegions) have default
--kind Type* -> Type;
--boxed datatypes have kind Type* -> Region -> Type* -> Type, where the
--param given by datatypeRegions[tycon] is the one of kind Region.
--If tycon has both a kind signature k and a datatype def tycon args = ...,
--k must have arity |args| and return a type.
--A tycon with a kind signature but no datatype definition may not return Type.
--End result: the kind of each tycon in scope is given a kind.

--Prim types and kinds have their kind given in Prim.evmc, which has already
--been imported into the module.

data KindCheckError = UnderappliedArrow
                    | TyNameNotInScope Name
                    | BadTyApp T T T T
                    | ShouldBeType T
                    | In String Name KindCheckError
  deriving (Eq,Ord,Read,Show)

--defuns: tysigs and all types in exprs must be Type
--static: all types must be type
--datatypes: given TyCon : ks -> Type, unify the args with ks and
--require all constructor params are :: Type.
--kind sigs do not have the same restriction, but all kinds must be well-kinded.
--Problem: I must check the kind of tyvars in type annotations and their kind
--should be consistent across multiple annotations.
--Must the kind check therefore be entangled with type inference...?
kindCheck :: Module -> Either KindCheckError ()
kindCheck m = do
  let kinds = kindsigs m --much simpler now thanks to Prim.evmc and FISK
  --I remove the globals to avoid an erroneous complaint that their regions
  --aren't types:
  --Aha, tysyns need to be emptied as well; tysyn bodies may contain any
  --kind.
  let m' = m{globals = M., tysyns = M.empty}
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
