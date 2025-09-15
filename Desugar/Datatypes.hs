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
import Control.Arrow ((***))

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
  tagScheme <- computeTagScheme tycon params cons' mr mti
  --Result: T, Map Name P.E (params have been normalized away)
  let conrhs = unrollTyApps (TyCon tycon) $ map TyVar params
  --Regardless of whether the datatype is boxed or not, we fill in its kind
  --here. TODO remove FIKS...
  defaultKindSig tycon params mr
  case mr of
    --The datatype is boxed; its tag is () and the tags are instead moved to
    --ImplCon1..ImplConN in the ImplTyCon datatype.
    --Con1 args => ImplTyCon (allocValue (ImplCon1 args))
    Just rvar -> do
      --data List r a = Nil | Cons {hd: a, tl: List r a} region r =>
      --data List r a = ImplList {unImplList: Ptr r (ImplList r a)}
      --data ImplList r a = ImplNil | ImplCons {implList_hd: a,
      --                                        implList_tl: List r a}
      let implcon = "Impl" ++ tycon
          implfield = "un" ++ implcon
          implconRHS = unrollTyApps (TyCon implcon) $
                       map TyVar params
      addDT tycon $ DTInfo {
        dtParams = params,
        dtRegion = mr,
        dtBoxed = True,
        dtTagScheme = tagScheme,
        dtCanonicalCons = [implcon] --map ("Impl"++) connames
        }
      --Add implcon as normal constructor of tycon
      addCon implcon $ Con {
        conBoxed = False,
        conParent = tycon,
        conFields = [(implfield, Ptr (TyVar rvar) implconRHS)],
        conRHS = conrhs
        }
      --Add its sole field (which is not boxed)
      addField implfield $ IsNormal {fiBoxed = False,
                                     fiParentTyCon = tycon,
                                     fiParentCon = implcon
                                    }
      --Add its boxed constructors (they'll be desugared away, but are needed
      --for type inference).
      --Note the tagScheme is inherited from the Impl datatype!
      addPerConInfo tycon conrhs tagScheme cons' True
      --Allocate the ImplTyCon datatype
      --prepend implTyCon_ to each field in each constructor
      let implConFields = map (("Impl"++) ***
                               map ((("impl"++tycon++"_")++) *** id)) cons'
      implcon `copyKindSigFrom` tycon
      addDT implcon $ DTInfo {
        dtParams = params,
        dtRegion = Nothing,
        dtBoxed = False,
        dtTagScheme = tagScheme,
        dtCanonicalCons = map fst implConFields
        }
      addPerConInfo implcon implconRHS tagScheme implConFields False
    --The datatype is unboxed
    Nothing -> do
      --Add DT info
      addDT tycon $ DTInfo {
        dtParams = params,
        dtRegion = mr,
        dtBoxed = False,
        dtTagScheme = tagScheme,
        dtCanonicalCons = connames
        }
      addPerConInfo tycon conrhs tagScheme cons' False

--A helper function for adding each con and field + tag; used to deduplicate
--the code in the boxed and unboxed case
addPerConInfo :: Name -> T -> TagScheme P.E -> [(Name,[(Name,T)])] ->
  Bool -> --whether the constructors are boxed
  PDT ()
addPerConInfo tycon conrhs tagScheme cons' boxed = do
  --Add per-con info
  sequence_ [do addCon con $ Con {
                  conBoxed = boxed,
                  conParent = tycon,
                  conFields = fields,
                  conRHS = conrhs
                  }
                --Add per-con info for each of its fields
                sequence_ [
                  addField field $ IsNormal {fiBoxed = boxed,
                                             fiParentTyCon = tycon,
                                             fiParentCon = con
                                            }
                  | (field,_t) <- fields
                  ]
            | (con,fields) <- cons']
  --Finally, add field info for .tagDT *iff the tag scheme is not Nil*
  if tagScheme /= Nil
    then addField ("tag"++tycon) $ IsTag {fiBoxed = boxed,
                                          fiParentTyCon = tycon
                                         }
    else return ()

computeTagScheme :: Name -> --tycon
         [Name] -> --params
         [(Name,[(Name,T)])] -> --con specs
         Maybe Name -> --region param if the datatype is boxed
         Maybe ([Name],T,Map Name P.E) -> --tag info if specified
         PDT (TagScheme P.E)
computeTagScheme tycon params cons mr mti =
  case mti of
    Nothing ->
      return $ let len = length cons
               in case () of
                    () | len <= 1 -> Nil
                       | len == 2 -> N1 1
                       | len > 16 -> N1 $ log256 $
                                     fromIntegral len
                       | let -> N16
    Just (tagParams,tagT, con2e) -> do
      -- the length of its params must match 'params'
      complainIf (length tagParams /= length params)
        $ TagParamDTParamLengthMismatch tycon params tagParams
      let tag2dtParams = M.fromList $ zip tagParams params
      --T may be free only in params; modify it to match the DT's params.
      --Note this'll break if I add rank-2 polymorphism
      tagTNorm <- everywhereM (mkM $ \case
                                  TyVar nm ->
                                    case M.lookup nm tag2dtParams of
                                      Nothing -> throwError $
                                        FreeVarInTagType nm tagT tycon
                                      Just nm' -> return $ TyVar nm'
                                  t -> return t) tagT
      --The tag-value mapping is given for the boxed constructors (Con),
      --but the resulting map is for their unboxed counterparts (ImplCon).
      let conset = S.fromList $ map fst cons
          specset = M.keysSet con2e
      complainIf (conset /= specset)
        $ ConMismatchInTagAndData tycon conset specset
      --Change: only prepend Impl if the datatype is boxed
      return $ Custom tagTNorm $ if mr /= Nothing
                                 then M.mapKeys ("Impl"++) con2e
                                 else con2e
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
addDT :: Name -> DTInfo P.E -> PDT ()
addDT = addThing datatypes (\m s -> s{datatypes=m}) "Datatype TyCon"

addCon :: Name -> ConInfo -> PDT ()
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
