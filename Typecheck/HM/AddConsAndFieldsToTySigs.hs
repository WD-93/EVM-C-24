module Typecheck.HM.AddConsAndFieldsToTySigs
  (addConsAndFieldsToTySigs) where

import AST.DTs
import AST.Util (unrollTyApps)

import Data.Map (Map(..))
import qualified Data.Map as M

--Splitting up the jumbo HM module bit by bit...
--field => .field : t
--Con => Con : t
addConsAndFieldsToTySigs :: Module -> Module
addConsAndFieldsToTySigs m =
  let di = dtsInfo m in
  m{tysigs = M.unions [tysigs m, conSigs di, fieldSigs di]}

--Good thing I cached conRHS!
conSigs :: DTsInfo e -> Map Name T
conSigs di = M.mapWithKey (\con ci ->
                             foldr (:->) (conRHS ci) $ map snd $ conFields ci
                          )
             $ conInfo di

--Can't use mapWithKey because the keys must be changed: field => .field
fieldSigs :: DTsInfo e -> Map Name T
fieldSigs di =
  M.fromList $
  map (\(field, fi) ->
         ('.':field,
          case fi of
            IsTag tycon ->
              --I presume reconstructing the rhs from ci is more efficient
              --than another M.! lookup of conInfo di.
              let dti = datatypes di M.! tycon
                  rhs = dtTagType dti
                  lhs = unrollTyApps (TyCon tycon) $ map TyVar $ dtParams dti
              in lhs :-> rhs
            IsNormal _ con ->
              let ci = conInfo di M.! con
                  lhs = conRHS ci --rhs becomes lhs because we're deconstr'ing
                  Just rhs = lookup field $ conFields ci
              in lhs :-> rhs
            )) $
  M.toList $ fieldInfo di
