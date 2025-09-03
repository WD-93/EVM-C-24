module Typecheck.HM.AddConsAndFieldsToTySigs
  (addConsAndFieldsToTySigs) where

import AST.DTs
import AST.Util (unrollTyApps,region2T,mkSig)

import Data.Map (Map(..))
import qualified Data.Map as M

--Splitting up the jumbo HM module bit by bit...
--field => .field : t
--Con => Con : t
--Change: now I make the order of the tyvars in schemes (forall vs . t)
--explicit; the ordering for Con : t is not by order of appearance in t, but
--the param order of the vars in the data decl.
--Example: Cons : forall r a . a -> List r a -> List r a
--Addition: for x : t; <region> x; we update its tysig to Ptr <region> t
addConsAndFieldsToTySigs :: Module -> Module
addConsAndFieldsToTySigs m =
  let di = dtsInfo m in
  m{tysigs = M.unions [updGlobalSigs m, conSigs di, fieldSigs di, tysigs m]}

updGlobalSigs :: Module -> Map Name Scheme
updGlobalSigs m =
  let gs = M.toList $ globals m
      ts = tysigs m
  in M.fromList $ do
    (g,(r,_me)) <- gs
    case M.lookup g ts of
      Just (params,t) -> return (g, (params,
                           Ptr (region2T r) t))
      Nothing -> [] --no signature to modify

--Good thing I cached conRHS!
--Change: the scheme params must be the datatype params.
--Since those params are always part of the constructor's type signature,
--that won't cause any unbound kind var errors.
--Note that existential qualification
--(e.g. data AST a = {App : AST (b -> a) -> AST b -> AST a}) is forbidden, so
--it's not a problem that the params can't include any vars other than the
--datatype params.
--I could extract the DT params from conRHS ci, but that would be hacky and
--asking for a bug... I instead get them from the canonical source:
--dtParams of the parent datatype's DT info.
conSigs :: DTsInfo e -> Map Name Scheme
conSigs di = M.mapWithKey (\con ci ->
                             let dt = conParent ci
                                 Just dti = M.lookup dt $ datatypes di
                                 params = dtParams dti
                             in (,) params $
                                foldr (:->) (conRHS ci) $ map snd $ conFields ci
                          )
             $ conInfo di

--Can't use mapWithKey because the keys must be changed: field => .field
fieldSigs :: Show e => DTsInfo e -> Map Name Scheme
fieldSigs di =
  M.fromList $
  map (\(field, fi) ->
         ('.':field,
          case fi of
            IsTag tycon ->
              --I presume reconstructing the rhs from ci is more efficient
              --than another M.! lookup of conInfo di.
              --Datatypes with the Nil tag scheme don't have a tag at all, but
              --since we see IsTag then dti will have a defined dtTagType.
              let dti = datatypes di M.! tycon
                  params = dtParams dti
                  rhs = dtTagType dti
                  lhs = unrollTyApps (TyCon tycon) $ map TyVar $ dtParams dti
              in (params, lhs :-> rhs)
            IsNormal _ con ->
              let ci = conInfo di M.! con
                  tycon = conParent ci
                  Just dti = M.lookup tycon $ datatypes di
                  params = dtParams dti
                  lhs = conRHS ci --rhs becomes lhs because we're deconstr'ing
                  Just rhs = lookup field $ conFields ci
              in (params, lhs :-> rhs)
            )) $
  M.toList $ fieldInfo di
