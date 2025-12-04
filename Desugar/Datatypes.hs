{-# LANGUAGE LambdaCase #-}
module Desugar.Datatypes (processDTs) where

--A module for processing DT decls: set default tags, allocate tag DTs,
--desugar boxed DTs.

import Util (complainIf,log256,(!))
import Desugar.DTs
import Desugar.T (desugarT)
import qualified E.Abs as P
import AST.Util
import Desugar.Util (defaultFieldName)
import DeclBucket (StaticThing(..))
import qualified DeclBucket as DB (ConInfo(..),FieldInfo(..))
import Import (PreModule(..))
import Desugar.SEP (desugarP, desugarE)
import Desugar.T (desugarT)

import Control.Monad (forM_)
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as M hiding ((!))
import qualified Data.Set as S
import Data.Generics (everywhereM,mkM)
import Control.Arrow ((***))
import Data.List (elemIndex)

{-
New approach:
The relevant info is stored in:
  pmStatThings :: MNL StaticThing, --data TyCon params = [Con], region r
  pmTagTypes :: MNL ([Located Name],T), --tag TyCon params = t
  pmConTags :: MNL (Name,E),            --Con of TyCon: e
  pmConstructors :: MNL ConInfo,        --Con {field: t}, boxity
  pmFields :: MNL FieldInfo             --Parent con, is tag
in PreModule.
Most conflicts have been eliminated (tycon, con, field, tagtype, contag),
but we must still:
 Generate tag schemes for each DT:
  Transfer tag decls from BoxedTyCon to ImplBoxedTyCon, checking for
  conflict with a preexisting manually declared tag scheme.
  Check the conTag ADecls from tag TyCon params = t where {Con1: e1, ...}
  cover exactly the constructors of TyCon.
  That requires the parent TyCon of the conTag ADecl is recorded, to prevent
  e.g.
   tag List r a = Byte where {False: 0, True: 1};
   tag Bool = Byte where {Nil: 0, Cons: 1}
  from being accepted.
-}

processDTs :: DInfo -> PreModule -> Either DError (DTsInfo E, Map Name T)
processDTs di pm = do
  --First we strip away location data
  let dts = M.mapMaybe (\case (STDatatype lparams cons mlr,_loc) ->
                                Just (map fst lparams,
                                      map fst cons,
                                      fst <$> mlr)
                              _ -> Nothing) $ pmStatThings pm
      --TODO fix inefficiency: I desugar each tag expr twice.
  tagTs <- mapM (\((lparams,pt,lcon_es),_loc) -> do
                    con_es <- mapM (\((con,_loc),pe) ->
                                       (,) con <$> desugarE di pe) lcon_es
                    return (map fst lparams,
                            desugarT pt,
                            con_es)) $
              pmTagTypes pm
  --DeclBucket's FieldInfo contains Locs while AST.DT's does not...
  --TODO move DB's definition to AST.DTs
  let cons = M.map (stripConInfo . fst) $ pmConstructors pm
      fields = M.map (stripFieldInfo . fst) $ pmFields pm
      kindsigs = M.map (desugarT . fst) $ pmKindSigs pm
  processDTs' dts tagTs cons fields kindsigs
  where stripConInfo :: DB.ConInfo -> ConInfo
        stripConInfo (DB.CI
                      boxed
                      (parent,_loc)
                      lnm_pts
                      pt) = Con boxed parent
                            (map (fst *** desugarT) lnm_pts)
                            (desugarT pt)
        stripFieldInfo :: DB.FieldInfo -> FieldInfo
        stripFieldInfo = \case
          DB.IsTag boxed (nm,_loc) -> IsTag boxed nm
          DB.IsNormal boxed (tycon,_loc1) (con,_loc2) ->
            IsNormal boxed tycon con
{-
Preconditions:
Tag field exists => its parent dt exists
Normal field exists => its parent dt and con exist
Con tag exists => its parent tagType exists
Con exists => its parent dt exists

Require:
A) For each tag TyCon params = t where {Con1: e; ...}:
1) data TyCon params' = cons exists and has equally many params
2) cons is exactly the cons in the tag decl
That requires checking each tagType and conTag.
B) If a boxed DT TyCon is declared, tag ImplTyCon may not be declared.

Problem: the boxed cons in BDTs aren't listed in one place.
Hack: look them up by dropping Impl from ImplTyCon's canonical cons.


--Filling in missing tag schemes:
For TyCon <- data:
 if not in tagSchemes, tagSchemes[TyCon] =
  if |cons| < 2: Nil
  if <= 16: N16
  else: N1 (log256 |cons|)

For each tag TyCon params = t where con_es:
 require data TyCon params' = cons
 require |params'| == |params|
 if the DT is boxed: 
 i
For each data TyCon params = cons, mr:
 if boxed:
  --tagged errors on param count mismatch
  If tagged:
   move tag decl to ImplTyCon
   require a tag Con for each ImplCon exists
   tag scheme = Nil
 else:
  If tagged:
   require a conTag for each canonical con exists
   tag scheme = Custom {...}
  else:
   tag scheme =
    If 0-1 cons: Nil
    If 2-16: N16
    Else: N1 (log256 numCons)

TODO: require each BDT TyCon has a kind sig, copy the kind sig to ImplTyCon,
require ImplTyCon doesn't already have one.
-}
processDTs' :: Map Name ( --data TyCon params = [Con], region r
  [Name], --params
  [Name], --unboxed cons
  Maybe Name --region
  ) ->
  Map Name ( --tag TyCon params = t
  [Name], --params
  T,
  [(Name,E)] --con tags
  ) ->
  Map Name ConInfo ->   --cons
  Map Name FieldInfo -> --fields
  Map Name T -> --kind sigs prior to defaulting
  Either DError (DTsInfo E, Map Name T)
processDTs' dts tagTs cons fields kindsigs = do
  --Custom tag schemes:
  (tycon2customTS,kindout) <- execStateT (setTagSchemes dts tagTs kindsigs)
    (M.empty,M.empty)
  --Filling in missing tag schemes:
  let dtis = M.mapWithKey (\tycon (params,cons,mr) ->
                              let ts = case M.lookup tycon tycon2customTS of
                                         Just (t,con2e) -> Custom t con2e
                                         Nothing ->
                                           case length cons of
                                             len | len < 2 -> Nil
                                                 | len <= 16 -> N16
                                                 | otherwise ->
                                                   N1 $ log256 $
                                                   fromIntegral len
                              in DTInfo{
                                dtParams = params,
                                dtRegion = mr,
                                dtBoxed = mr /= Nothing, --redundant...?
                                dtTagScheme = ts,
                                dtCanonicalCons = cons
                                }) dts
  --TODO require r exists in params for boxed data TyCon params ... region r
  return (DTsInfo{
             datatypes = dtis,
             conInfo = cons,
             fieldInfo = fields
             },
           kindout)

--Set tag scheme monad
--Only needs to deal with custom tag schemes
type STS = StateT (Map Name (T, Map Name E), --tag schemes
                   Map Name T --kindout
                  ) (Either DError)
{-
Algo:
TODO default kind sigs here
TODO kindout = {}
tagSchemes = {}
For TyCon <- union of tag and data keys:
 if data does not exist: fail
 TODO:
  Set kindout
 if tag exists:
  if TyCon is boxed:
   look up ImplTyCon, require it has an ImplCon for each Con:e tag and vv
   tagSchemes[ImplTyCon] = Custom{ImplCon:e}
  else:
   require TyCon has a Con for each Con:e tag and vv
   tagSchemes[TyCon] = Custom{Con:e}
Setting tagSchemes should fail if you try to do it twice for a key;
since tag decls have been deconflicted, that's only possible if a tag has
been declared for ImplTyCon.

If a DT is boxed, its kind should default to Type*->Region->Type*->Type,
where r is Region. Enforce r in params here.
If it's Impl, it should default to the same as its parent.
Otherwise, it should default to Type*->Type.
Unboxed default:
 If kindout[tycon] hasn't already been set:
  set based on params and kindin[tycon]
Boxed default:
 Set kindout[tycon] based on params and kindin[tycon]; it won't have been set.
 Set kindout[ImplTyCon] to the same unless kindin[ImplTyCon] exists
Dominance order for ImplTyCon: explicit kindsig > parent > boxed default.

Enforce: r must be Region even if tycon is given an explicit kind signature.
If it's not present in params, fail.
-}
setTagSchemes :: Map Name ([Name],    --params
                           [Name],    --canonical cons
                           Maybe Name --region
                          ) ->
                 Map Name ([Name],    --params
                           T,         --tag type
                           [(Name,E)] --con tags
                          ) ->
                 Map Name T -> --kind sigs before defaulting
                 STS ()
setTagSchemes dts tags kindin =
  forM_ (S.union (M.keysSet dts) (M.keysSet tags))
  (\tycon -> 
      case M.lookup tycon dts of
        Nothing -> throwError $ TagDeclOfNonexistentDT tycon
        Just (params,cons,mr) -> do
          goKindSigs tycon params mr
          goTagSchemes tycon params cons mr)
  where
    goKindSigs :: Name -> [Name] -> Maybe Name -> STS ()
    goKindSigs tycon params mr = do
      k <- lift $ defaultKind (M.lookup tycon kindin) params mr
      case mr of
        Nothing -> weakSet tycon k
        Just r -> do
          case M.lookup ("Impl"++tycon) kindin of
            Nothing -> strongSet ("Impl"++tycon) k
            _ -> return ()
          strongSet tycon k
    strongSet :: Name -> T -> STS ()
    strongSet tycon k = modify $ id *** M.insert tycon k
    weakSet :: Name -> T -> STS ()
    weakSet tycon k = do
      ks <- gets snd
      if M.member tycon ks
        then return ()
        else strongSet tycon k
    goTagSchemes tycon params cons mr =
      case M.lookup tycon tags of
        Nothing -> return ()
        Just (params',t,con_es) -> do
          complainIf (length params /= length params')
            $ TagParamDTParamLengthMismatch tycon params' params
          case mr of
            Nothing ->
              setTagScheme tycon params params' t cons con_es
            Just _ -> do
              let impltycon = "Impl"++tycon
              case M.lookup impltycon dts of
                Nothing ->
                  error "Compiler error: this should never happen!"
                Just (_,implcons,_) ->
                  setTagScheme impltycon params params' t implcons $
                  map (("Impl"++)***id) con_es
--Given maybe kind sig, params and maybe a region param r, returns the DT's
--kind. Errors if:
--1) r is not present in params
--If there is a kind signature:
--2) the given kind signature is not concrete (does not ultimately return a
--Type) or has the wrong arity.
--3) r is given a non-Region kind
defaultKind :: Maybe T -> [Name] -> Maybe Name -> Either DError T
defaultKind ksig params mr = do
  --1)
  mix <- case mr of
           Nothing -> return Nothing
           Just r ->
             case elemIndex r params of
               Nothing -> throwError $ RegionTyVarNotInParams r params
               Just ix -> return $ Just ix
  case ksig of
    --If there is a kind signature
    Just k -> do
      let (ts,ret) = rollFunApps k
      --2a)
      complainIf (length ts /= length params)
        $ KindSigParamArityMismatch k params
      --2b)
      complainIf (ret /= TyCon "Type")
        $ DTKindSigIsNotConcrete k
      --3)
      case mix of
        Nothing -> return ()
        Just ix -> complainIf ((ts !! ix) /= TyCon "Region")
                   $ RegionTyVarGivenNonRegionKind k mr params
      return k
    --Compute default
    Nothing ->
      let ts = [TyCon $ if Just param == mr then "Region" else "Type"
               | param <- params]
      in return $ unrollFunApps (ts, TyCon "Type")
      
--Duplicate con tags has already been caught
--The tag type is in scope tagparams; they need to be substituted for dtparams
--in t. No substitution need be done for con_es since they're not in scope
--there.
setTagScheme :: Name -> [Name] -> [Name] -> T -> [Name] -> [(Name,E)] ->
  STS ()
setTagScheme tycon dtparams tagparams tagT cons con_es = do
  s <- gets fst
  case M.lookup tycon s of
    Just ts' -> throwError $ DuplicateTagDecls tycon
    Nothing -> do
      --Precondition: they're of equal length
      let tag2dtParams = M.fromList $ zip dtparams tagparams
      --Note this'll break if I add rank-2 polymorphism
      tagTNorm <- everywhereM (mkM $ \case
                                  TyVar nm ->
                                    case M.lookup nm tag2dtParams of
                                      Nothing -> throwError $
                                        FreeVarInTagType nm tagT tycon
                                      Just nm' -> return $ TyVar nm'
                                  t -> return t) tagT
      --Precondition: no duplicate (con,E) pairs in con_es,
      --no duplicate contructors in cons
      let con2e = M.fromList con_es
          conSet = S.fromList cons
          taggedSet = M.keysSet con2e
      complainIf (conSet /= taggedSet)
        $ TagSetConSetMismatch tycon taggedSet conSet
      modify (M.insert tycon (tagTNorm,con2e) *** id)

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

{-
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
-}
{-
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
-}
