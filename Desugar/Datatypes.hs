{-# LANGUAGE LambdaCase #-}
module Desugar.Datatypes where

--A module for processing DT decls: set default tags, allocate tag DTs,
--desugar boxed DTs.

import Util (complainIf,log256,(!))
import Desugar.DTs
import Desugar.T (desugarT)
import qualified E.Abs as P
import AST.Util
import Desugar.Util (defaultFieldName)

import Control.Monad (forM_)
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as M hiding ((!))
import qualified Data.Set as S
import Data.Generics (everywhereM,mkM)

-- ***********Copied from Desugar.Desugar:

--Boxed datatype data TyCon params = Con1 args | ... region r =>
--data TyCon params = ImplCon1 (Ptr r (StructCon1 params)) | ...
--If TyCon does not have a tag decl, default it.
--data StructCon1 params = StructCon1 args
--Move TyCon's tags to StructCon1 ... StructConN; replace with ().
--End result: boxed datatypes not fully eliminated, since desugaring of
--BoxedCon exprs and patterns is deferred until after TC.

--E: Con1 args => ImplCon1 (allocValue (StructCon1 args))
--P: case x of Con1 args -> ... =>
--case x of ImplCon1 ptr -> let StructCon1 args = *ptr in ...
--bdt.field =>
--case bdt of ImplCon p -> (*p).fieldCon --for each con containing field
--I can eliminate .field, but what about .field=?
--I won't eliminate either, it's simpler to deal with the fallout of fields
--shared between constructors during monomorphic compilation.
-- .tagDT is special in that it's to the left of the padding...
--It should be accessible to the user to get and set, so might as well keep
--using the field syntax + naming convention.

--Add tagDT field to each con if tag type and values are not specified
--Repr decl:
--tag TyCon params = t where {Con: e}
--It's (UInt 0) if DT is struct-like. Allow 0-sized ints rather than having
--a no-tag exception for ()-like datatypes!
--It's UInt <log256 con count> if DT is union-like
--Note ints shouldn't have any fields, ensuring they're the leaves of the repr.
--Otherwise it's TagDT; allocate data TagDT = TagCon1 | ..., a union-like
--datatype.
--Associate each constructor with a static value.
--Convert each Con ts => Con {fieldCon<N>: t}
--Require:
--No duplicate constructors
--No duplicate params within same DT
--No duplicate ordinary fields; only tagDT may be shared
--For each DT, its tag decl specifies the value of each constructor in its
--listing (ImplCons is in List; Cons is not).

processDTs :: Map Name ([Name],P.DataRHS) -> --datatypes
              Map Name ([Name], T, Map Name P.E) -> --tag decls
              Map Name T -> --kind signatures!
              Either DError (DTsInfo P.E, Map Name T)
processDTs dts tds ks =
  runExcept $ execStateT go (DTsInfo M.empty M.empty M.empty, ks)
  where go = do
          let dts' = M.toList dts
          sequence_ [
            do let (conspecs,mr) = desugarDataRHS datarhs
               processDT tycon params conspecs mr (M.lookup tycon tds)
            | (tycon,(params,datarhs)) <- dts']
desugarDataRHS :: P.DataRHS -> ([(Name,Either [(Name,T)] [T])], Maybe Name)
desugarDataRHS = \case
  P.Boxed urhs (Ident r) -> (desugarURHS urhs, Just r)
  P.Unboxed urhs -> (desugarURHS urhs, Nothing)
desugarURHS (P.URHS datacons) = map desugarDataCon datacons
desugarDataCon = \case
  P.DCArgs dca ->
    let (con,ts) = desugarDCA dca
    in (con, Right ts)
  P.DCRecord (UIdent con) recordfields ->
    let fields = map desugarRecordField recordfields
    in (con, Left fields)
desugarDCA :: P.DCA -> (Name,[T])
desugarDCA = go
  where go = \case
          P.DCANil (UIdent con) -> (con,[])
          P.DCACons dca pt ->
            --I know it's quadratic...
            let (con,ts) = go dca
            in (con, ts ++ [desugarT pt])
desugarRecordField :: P.RecordField -> (Name,T)
desugarRecordField (P.RF (Ident field) pt) = (field,desugarT pt)

--Process DTs monad
type PDT = StateT (DTsInfo P.E, Map Name T) (Except DError)
processDT :: Name -> --tycon
         [Name] -> --params
         [(Name,Either [(Name,T)] [T])] -> --con specs
         Maybe Name -> --region param if the datatype is boxed
         Maybe ([Name],T,Map Name P.E) -> --tag info if specified
         PDT ()
processDT tycon params cons mr mti = do
  --First, add default field names for Con args constructors
  let cons' = map (\(con,ei_fs_ts) ->
                     (con, case ei_fs_ts of
                             Left fs -> fs
                             Right ts -> zip (map (defaultFieldName con) [1..])
                                         ts)) cons
      connames = map fst cons'
  --Compute tag info
  (tagT,con2tag) <- case mti of
    --If it's specified:
    Just (tagParams,tagT,con2e) -> do
      -- the length of its params must match 'params'
      complainIf (length tagParams /= length params)
        $ TagParamDTParamLengthMismatch tycon params tagParams
      let tag2dtParams = M.fromList $ zip tagParams params
      -- T may be free only in params; modify it to match the DT's params.
      --Note this'll break if I add rank-2 polymorphism
      tagTNorm <- everywhereM (mkM $ \case
                                  TyVar nm ->
                                    case M.lookup nm tag2dtParams of
                                      Nothing -> throwError $
                                        FreeVarInTagType nm tagT tycon
                                      Just nm' -> return $ TyVar nm'
                                  t -> return t) tagT
       -- the map's keys must be exactly the con set
      let conset = S.fromList $ map fst cons'
          specset = M.keysSet con2e
      complainIf (conset /= specset)
        $ ConMismatchInTagAndData tycon conset specset
      return (tagTNorm,con2e)
    Nothing
      --If unspecified: default
      --If union-like: UInt n for minimal n
      --Note this case must be before the one for 0 or 1 constructors to avoid
      --Unit being tagged with Unit.
      | all (\(_con,fields) -> null fields) cons' ->
        let numCons = fromIntegral $ length cons'
            bytesz = log256 numCons
        in return (UInt $ fromIntegral bytesz,
                   M.fromList $ zip connames $ map P.Int [0..])
      --If 0 or 1 constructors: ()
      | length cons' <= 1 ->
        return (TyCon "Unit", M.fromList $ zip connames $ repeat $
                              P.Con $ UIdent "Unit")
      
      --Otherwise allocate union-like DT TagDT = TagCon1 .. TagConN and use
      --respective constructors as tags.
      | let -> do
          let tagDT = "Tag"++tycon
          processDT tagDT [] [("Tag"++con, Right []) | con <- connames]
            Nothing Nothing
          return (TyCon tagDT, M.fromList [(con, P.Con $ UIdent $ "Tag"++con)
                                          | con <- connames])
  --Result: T, Map Name P.E (params have been normalized away)
  let conrhs = unrollTyApps (TyCon tycon) $ map TyVar params
  --Regardless of whether the datatype is boxed or not, we fill in its kind
  --here. TODO remove FIKS...
  defaultKindSig tycon params mr
  case mr of
    --The datatype is boxed; its tag is () and the tags are instead moved to
    --StructCon1..StructConN.
    --Its constructors Con fields are replaced with
    --ImplCon (Ptr r (StructCon params))
    Just rvar -> do
      addDT tycon $ DTInfo {
        dtParams = params,
        dtRegion = mr,
        dtTagType = TyCon "Unit",
        dtCanonicalCons = map ("Impl"++) connames
        }
      --For each Con args, allocate
      --data StructCon params = StructCon args
      --tag StructCon params = tagT where {StructCon: con2tag M.1 con}
      --Addition: copy the kind signature from the parent TyCon to each
      --StructCon!
      sequence_ [
        do let scon = "Struct" ++ con
           scon `copyKindSigFrom` tycon
           processDT scon params
             [(scon, Left $ map (\(fld,t) -> (fld++scon,t)) fields)]
             Nothing
             (Just (params,tagT,M.singleton scon $ con2tag ! con))
           let implfield = "unImpl" ++ con
               implcon = "Impl" ++ con
           addCon implcon $ UBCon {
             conParent = tycon,
             conTag = P.Con (UIdent "Unit"),
             conFields = [(implfield,
                           Ptr (TyVar rvar) $ unrollTyApps (TyCon scon) $
                           map TyVar params)],
             conRHS = conrhs
             }
             --Changed to IsNormal False - is that correct?
           addField implfield $ IsNormal False implcon
           --Now we add the boxed con it desugars from
           addCon con $ BCon {
             conParent = tycon,
             conFields = fields,
             conRHS = conrhs
             }
           --xs.hd will not be present in E, but it will in Cons {hd: p}
           --Q: should it be IsNormal True?
           forM_ fields $ \(field,t) ->
             addField field $ IsNormal True con
        | (con,fields) <- cons']
    --The datatype is unboxed
    Nothing -> do
      --Add DT info
      addDT tycon $ DTInfo {
        dtParams = params,
        dtRegion = mr,
        dtTagType = tagT,
        dtCanonicalCons = connames
        }
      --Add per-con info
      sequence_ [do
        addCon con $ UBCon {
            conParent = tycon,
            conTag = con2tag ! con,
            conFields = fields,
            conRHS = conrhs
            }
        --Add per-con info for each of its fields
        sequence_ [
          addField field $ IsNormal False con
          | (field,_t) <- fields
          ]
        | (con,fields) <- cons']
      --Finally, add field info for .tagDT
      addField ("tag"++tycon) $ IsTag tycon

--The below three add functions add a DT, Con and Field to the DTsInfo state
--respectively.
--It makes sense to throw duplicate errors here despite an earlier
--check in Desugar.Desugar, because datatype desugaring creates new
--datatypes and constructors (ImplCon, StructCon and TagCon).
--I've decided against adding a param which indicates whether the thing is
--generated or from source, as future previous passes may also generate
--datatypes and that would risk confusing it.
--A generated param would also need to be added to processDT because it
--recursively generates tag datatypes.
addDT :: Name -> DTInfo -> PDT ()
addDT = addThing datatypes (\m s -> s{datatypes=m}) "Datatype TyCon"

addCon :: Name -> ConInfo P.E -> PDT ()
addCon = addThing conInfo (\m s -> s{conInfo=m}) "Constructor"

addField :: Name -> FieldInfo -> PDT ()
addField = addThing fieldInfo (\m s -> s{fieldInfo=m}) "Field"

addThing :: ((DTsInfo P.E) -> Map Name v) -> --getter
            (Map Name v -> DTsInfo P.E -> DTsInfo P.E) -> --setter
            String -> --kind of thing to add
            Name -> v -> PDT ()
addThing getter setter typ nm v = do
  (s,ks) <- get
  let m = getter s
  case M.lookup nm m of
    Just conflict ->
      throwError $ Duplicate typ nm
    Nothing -> put (setter (M.insert nm v m) s,ks)

--Boxed datatypes such as List r a must always have an explicit kind
--signature; the derived tycons StructNil, StructCons must be given the same
--signature!
copyKindSigFrom :: Name -> Name -> PDT ()
copyKindSigFrom to from = do
  (s,ks) <- get
  case M.lookup from ks of
    Nothing -> throwError $ BoxedTyConLacksKindSig from
    Just k ->
      case M.lookup to ks of
        Just k' -> throwError $ StructDTAlreadyGivenKindSig to k'
        Nothing -> put (s, M.insert to k ks)

--Sets the datatype tycon's kind sig.
--If it already has one: do nothing.
--If it's unboxed: Type* -> Type
--If it's boxed: change r's kind to Region.
defaultKindSig :: Name -> [Name] -> Maybe Name -> PDT ()
defaultKindSig tycon params mr = do
  (s,ks) <- get
  let ty = TyCon "Type"
      re = TyCon "Region"
  if M.member tycon ks
    then return ()
    else do
    let k = foldr (:->) (TyCon "Type")
                 [if Just param == mr
                  then re
                  else ty
                 | param <- params
                 ]
    put (s, M.insert tycon k ks)
