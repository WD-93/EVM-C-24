{-# LANGUAGE LambdaCase, DeriveLift, StandaloneDeriving #-}
module DeclBucket where

--Modules are converted into DeclBuckets after initial parsing, since we might
--as well group declarations logically after we scan them for imports.
--Doing basic CST parsing and conflict detection here also simplifies Desugar,
--letting it focus on proper desugaring.

--Longer explanation:
--After parsing, an EVMC module is simply a list of declarations.
--Those declarations usually do not form a complete, compilable program on
--their own; for example, they may refer to globals or functions defined in
--another module.
--Compilation assumes a namespace of modules, one of which is selected to be
--the main module; the final result is a single module containing the
--declarations of the main module and its transitive dependencies.
--A dependency on another module is indicated via the 'import <modulename>'
--declaration; note duplicate imports are ignored.

--The .evmc files in the Stdlib folder are all collected into a namespace at
--(Haskell) compile time using Template Haskell. However, that won't do for
--user programs - recursively scanning the current directory for .evmc files
--whenever they compile a module is wasteful.
--Given a command to compile SomeModule.evmc, the first matching file is
--found from the path. The file is then parsed and added to the existing
--namespace. The procedure continues recursively on the imported modules
--(ignoring module names already in the namespace).
--Most declarations are not imports. Since we need to parse each module and
--iterate over its declarations anyway, we might as well bucket them logically
--and complain if there are obvious conflicts.
--That is the purpose of the DeclBucket data structure: it sorts each
--declaration type into its own bucket and attributes each decl to a module so
--it can be blamed on conflict.

import E.Abs hiding (M(),D(),S(),E(),T(),hasPosition,HasPosition())
import qualified E.Abs as E
import AST.DTs (Name(..),Region(..))
import Desugar.Util (defaultFieldName)

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Arrow ((***))
import Language.Haskell.TH.Syntax (Lift())

--First: associate each syntax node not just with its location in the module
--but with the module name.
--Why is it a Maybe ModLoc??
addModName :: Functor f => ModName -> f (Maybe ModLoc) -> f Loc
addModName mnm = fmap (\mml ->
                         (mnm, case mml of
                                 Nothing -> (-1,-1) --ugly...
                                 Just ml -> ml))
--Location within a module file:
type ModLoc = (Int,Int) -- = BNFC'Position
--Location within a namespace:
type Loc = (ModName,ModLoc)
type ModName = [Name] --Foo.Bar.Baz
type Located a = (a,Loc)
type MSL a = Map Name (Set (Located a))
type B a = (Name, Located a)

type M = E.M' Loc
type D = E.D' Loc
type S = E.S' Loc
type E = E.E' Loc
type T = E.T' Loc

--Identical instance types will eventually be caught by the type checker...
--Since the bucket will now contain a set, I might as well just key it by the
--function name.
--Validity condition for dyn things: the map is a singleton or all instances.
--Decls should be located by their starting pos.
--For most atomic decls, that's the decl's... but not for con, field and con
--tag adecls.
--import may fail for a module not in the namespace.

--I don't strictly need this DT, but using it instead of a bucket directly
--ensures each ADecl is one binding - no more, no less.
data ADecl = ADefault (B T)
           | ATySig (B T)
           | AKindSig (B T)
           | ADynThing (B DynamicThing)
           | AStatThing (B StaticThing)
           | ACon (B ConInfo)
           | AField (B FieldInfo)
           --By keeping the Con:e map in TagType we can avoid a traversal of
           --all con tags later.
           | ATagType (B ([Located Name],T,[(Located Name,E)]))
           --The E is now redundant, but might as well cache it for cheaper
           --error reporting.
           | AConTag (B (Name,E))
           | AImport (Located ModName)
  deriving (Eq,Ord,Read,Show)
data DeclBucket = DB {
  dbDefaults :: MSL T, --loc->"default ..."
  --tySigs should not include fields or cons
  dbTySigs :: MSL T, --loc->"f : ..."
  dbKindSigs :: MSL T,
  dbDynThings :: MSL DynamicThing,
  dbStatThings :: MSL StaticThing,
  dbTagTypes :: MSL ([Located Name],T,[(Located Name, E)]),
  dbConTags :: MSL (Name,E),
  dbConstructors :: MSL ConInfo,
  dbFields :: MSL FieldInfo,
  dbImports :: Set (Located ModName)
  }
  deriving (Eq,Ord,Read,Show,Lift)
--Boilerplate, but at least Haskell writes most of it
--An AutoDeriveChildren extension would make this one line.
deriving instance Lift a => Lift (S' a)
deriving instance Lift a => Lift (T' a)
deriving instance Lift a => Lift (E' a)
deriving instance Lift Region
deriving instance Lift a => Lift (EField' a)
deriving instance Lift Ident
deriving instance Lift a => Lift (AOp' a)
deriving instance Lift HexInteger
deriving instance Lift UIdent
deriving instance Lift a => Lift (CASE' a)
deriving instance Lift a => Lift (VarBind' a)
--D' instance to support contract objects
deriving instance Lift a => Lift (D' a)
deriving instance Lift a => Lift (ModuleName' a)
deriving instance Lift a => Lift (GlobalRegion' a)
deriving instance Lift a => Lift (DataRHS' a)
deriving instance Lift a => Lift (UnboxedRHS' a)
deriving instance Lift a => Lift (DataCon' a)
deriving instance Lift a => Lift (DCA' a)
deriving instance Lift a => Lift (RecordField' a)
deriving instance Lift a => Lift (ConArgs' a)
deriving instance Lift a => Lift (ConTag' a)

--What possible conflicts are there?
--Tysigs and kind sigs form their own maps; for datatypes a kind sig is
--optional.
--Functions and globals
data DynamicThing = DTDefun (E,S)
                  | DTInstance (T,E,S)
                  | DTGlobal (Region, Maybe E)
                  | DTContract [D]
  deriving (Eq,Ord,Read,Show,Lift)
--Datatypes and tysyns
--Might as well Locate everything
data StaticThing = STDatatype [Located Name] --typarams
                   [Located Name] --canonical constructors
                   (Maybe (Located Name)) --r if boxed
                 | STTySyn [Located Name] T
  deriving (Eq,Ord,Read,Show,Lift)
data ConInfo = CI {ciBoxed :: Bool,
                   ciParent :: Located Name,
                   ciFields :: [(Located Name,T)],
                   ciRHS :: T
                  }
  deriving (Eq,Ord,Read,Show,Lift)
data FieldInfo = IsTag {fiBoxed :: Bool, fiParentTyCon :: Located Name}
               | IsNormal {fiBoxed :: Bool,
                           fiParentTyCon :: Located Name,
                           fiParentCon :: Located Name}
  deriving (Eq,Ord,Read,Show,Lift)
emptyBucket = DB e e e e e e e e e S.empty
  where e :: Map k v
        e = M.empty
unionBucket (DB a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)
  (DB b1 b2 b3 b4 b5 b6 b7 b8 b9 b10) =
  DB (u a1 b1) (u a2 b2) (u a3 b3) (u a4 b4) (u a5 b5) (u a6 b6) (u a7 b7)
  (u a8 b8) (u a9 b9) (S.union a10 b10)
  where u m1 m2 = M.unionWith S.union m1 m2
unionBuckets :: Foldable t => t DeclBucket -> DeclBucket
unionBuckets dbs = foldr unionBucket emptyBucket dbs

adeclToBucket :: ADecl -> DeclBucket
adeclToBucket = \case
  ADefault (k,v) -> e{dbDefaults=s k v}
  ATySig (k,v) -> e{dbTySigs=s k v}
  AKindSig (k,v) -> e{dbKindSigs=s k v}
  ADynThing (k,v) -> e{dbDynThings=s k v}
  AStatThing (k,v) -> e{dbStatThings=s k v}
  ACon (k,v) -> e{dbConstructors=s k v}
  AField (k,v) ->e{dbFields=s k v}
  ATagType (k,v) -> e{dbTagTypes=s k v}
  AConTag (k,v) -> e{dbConTags=s k v}
  AImport mnm -> e{dbImports=S.singleton mnm}
  where e = emptyBucket
        s k v = M.singleton k $ S.singleton v

declToADecls :: D -> [ADecl]
declToADecls = \case
  Default loc (UIdent nm) t -> binding ADefault loc nm t
  TySig loc (Ident nm) t -> binding ATySig loc nm t
  KindSig loc (UIdent nm) t -> binding AKindSig loc nm t
  --Dyn things
  Defun loc (Ident nm) e s -> binding ADynThing loc nm $ DTDefun (e,s)
  Instance loc (Ident nm) t e s -> binding ADynThing loc nm $ DTInstance (t,e,s)
  Global loc gr vb ->
    let r = globalRegionToRegion gr
        (nm,me) = desugarVarBind vb
    in binding ADynThing loc nm $ DTGlobal (r,me)
  --Stat things
  Data loc ca drhs -> dataToADecls loc ca drhs
  TySyn loc ca t ->
    let (con,params) = desugarConArgs ca
    in binding AStatThing loc (fst con) $ STTySyn params t
  --DT tags
  Tag loc ca t ct -> tagToADecls loc ca t ct
  Import loc m -> [AImport (parseModuleName m,loc)]
  Contract loc (Ident nm) ds -> binding ADynThing loc nm $ DTContract ds
binding :: (B a -> ADecl) -> Loc -> Name -> a -> [ADecl]
binding con loc nm v = [con (nm,(v,loc))]
--data TyCon args = { --Static thing data binding, tag field
-- Con { --Con binding
--  field: t, --Field binding
--  ...
-- };
-- ...
--}
--If TyCon is boxed, give it a single constructor ImplTyCon
--data List r a = Nil | Cons {hd: a, tl: List a} region r; =>
--data List r a = ImplList (Ptr r (ImplList r a));
--data ImplList r a = ImplNil | ImplCons {impl
--Nil, Cons, hd and tl must be declared as boxed cons and fields respectively
--to enable desugaring when they occur in source.
-- .tagList and .tagImplList must also be declared.
--Their type is not yet specified, however; if
--tag List r a = t where {Nil: e1, Cons: e2}, the tag type and con tags will
--need to be moved to ImplList.
--Should I should record boxed cons alongside region in boxed DTs?
--It's possible to reconstruct them from ImplTyCon's canonical cons...
dataToADecls :: Loc -> ConArgs' Loc -> DataRHS' Loc -> [ADecl]
dataToADecls loc ca drhs =
  let (tycon,params) = desugarConArgs ca
      (urhs,mr) = case drhs of
                    --Huh, I can only get r's approximate loc
                    Boxed rloc urhs (Ident r) -> (urhs, Just (r,rloc))
                    Unboxed _ urhs -> (urhs, Nothing)
      URHS _loc rhs = urhs
      lcon_fields = map desugarDataCon rhs
  in mkData loc (fst tycon) params lcon_fields mr
mkData :: Loc -> --data decl loc
          Name -> --tycon
          [Located Name] -> --params
          [(Located Name, [(Located Name, T)])] -> --cons
          Maybe (Located Name) -> --region var
          [ADecl]
mkData loc tycon params lcon_fields mr =
  case mr of
    Just r ->
      --Declare boxed constructors and their fields
      (do ((con,cloc),fields) <- lcon_fields
          binding ACon cloc con CI{
            ciBoxed = True,
            ciParent = (tycon,loc),
            ciFields = fields,
            ciRHS = tapps (tcon tycon) (map tvar params)
            } ++
            do ((field,floc),t) <- fields
               binding AField floc field IsNormal{
                 fiBoxed = True,
                 fiParentTyCon = (tycon,loc),
                 fiParentCon = (con,cloc)
                 }) ++
      --data List r a = ImplList {unImplList: Ptr r (ImplList r a)}
      mkUBCons loc tycon params [(("Impl"++tycon,loc),
                                  [(("unImpl"++tycon,loc),
                                    --Ptr r (ImplTyCon params)
                                    ptr_r r tycon params)])] (Just r)
      ++
      --data ImplList r a = ImplNil
      --                  | ImplCons {
      --                     implList_hd: a,
      --                     implList_tl: List a
      --                    }
      mkUBCons loc ("Impl"++tycon) params (map (\((con,loc),fields) ->
                                                  (("Impl"++con,loc),
                                           map (\((fld,loc),t) ->
                                                  (("impl"++tycon++"_"++fld,
                                                    loc),t)) fields))
                                           lcon_fields) Nothing
    Nothing ->
      mkUBCons loc tycon params lcon_fields Nothing
  where
    --Annoyingly, I must use the data loc for everything here since the
    --type is generated. I must also implement unrollTyApps for T'...
    ptr_r r tycon params =
      --Ptr r (ImplTyCon params)
      (tcon "Ptr" `tapp` tvar r) `tapp`
      tapps (tcon $ "Impl"++tycon) (map tvar params)
    tcon = TCon loc . UIdent
    tvar (var,vloc) = TVar vloc $ Ident var
    tapp = TApp loc
    tapps = foldl tapp
            
--Given the canonical constructors, generates the tycon, con and field
--bindings.
mkUBCons :: Loc -> --data decl loc
            Name -> --tycon
            [Located Name] -> --params
            [(Located Name, [(Located Name, T)])] -> --cons
            Maybe (Located Name) -> --region var
            [ADecl]
mkUBCons loc tycon params lcon_fields mr =
  --data TyCon params = ...
  binding AStatThing loc tycon (STDatatype params
                                 (map fst lcon_fields) mr) ++
  --EDIT: not every DT has a tag! I instead generate the tags and check for
  --clashes in Desugar.Desugar, after tag scheme generation.
  --tagTyCon is a tag field; it's boxed iff mr /= Nothing
  --binding AField loc ("tag"++tycon) IsTag{fiBoxed = mr /= Nothing,
  --                                        fiParentTyCon = (tycon,loc)
  --} ++
  --For Con fields
  do ((con,cloc),fields) <- lcon_fields
     binding ACon loc con (CI {ciBoxed = False,
                               ciParent = (tycon,loc),
                               ciFields = fields,
                               ciRHS = foldl tapp (tcon (tycon,loc))
                                       (map tvar params)
                              }) ++
       --For fields
       do ((field,cloc),t) <- fields
          binding AField loc field IsNormal {fiBoxed=False,
                                             fiParentCon=(con,cloc),
                                             fiParentTyCon=(tycon,loc)
                                            }
       where
         tcon (con,loc) = TCon loc (UIdent con)
         tvar (var,loc) = TVar loc (Ident var)
         tapp = TApp loc
parseModuleName :: ModuleName' a -> ModName
parseModuleName = go
  where go = \case
          MNil _ (UIdent nm) -> [nm]
          MCons _ (UIdent nm) mnm -> nm:go mnm
--Defaults the fields in a DataCon if it's in arg form (Cons a (List a)),
--returning (con,field_ts).
--For now, defaultFieldName con n lives in Desugar.Util.
--The location of the fields must also be returned for the AField ADecls.
--For implicit fields, their loc is the same as their T.
desugarDataCon :: DataCon' Loc -> (Located Name, [(Located Name, T)])
desugarDataCon = \case
  DCArgs loc dca ->
    let (lcon@(con,_),ts) = desugarDCA dca
    in (lcon, zipWith (\n t ->
                         let loc = hasPosition t
                         in ((defaultFieldName con n, loc),t)) [1..] ts)
  DCRecord loc (UIdent con) rfs ->
    let field_ts = map (\(RF loc (Ident f) t) -> ((f,loc),t)) rfs
    in ((con,loc),field_ts)
desugarDCA :: DCA' Loc -> (Located Name, [T])
desugarDCA = (id *** reverse) . go
  where go = \case
          DCANil loc (UIdent con) -> ((con,loc),[])
          DCACons _loc dca t -> (id *** (t:)) $ go dca
--tag TyCon args = t where { --tagType ADecl
-- Con: e, --conTag decl
-- ...
-- }
tagToADecls :: Loc -> ConArgs' Loc -> T -> [ConTag' Loc] -> [ADecl]
tagToADecls loc ca t cts =
  let ((tycon,_loc),params) = desugarConArgs ca
      lcon_es = do
        ConTag loc (UIdent con) e <- cts
        return ((con,loc),e)
  in binding ATagType loc tycon (params,t,lcon_es) ++ do
    ((con,loc),e) <- lcon_es
    binding AConTag loc con (tycon,e)

--TODO propagate the location info? When something goes wrong with a global's
--region I can just report the location of the global binding...
globalRegionToRegion :: GlobalRegion' a -> Region
globalRegionToRegion = \case
  Memory _ -> Me
  Storage _ -> St
  TStorage _ -> TS
  Code _ -> Co
desugarVarBind :: VarBind' Loc -> (Name, Maybe E)
desugarVarBind = \case
  JustVar _ (Ident nm) -> (nm, Nothing)
  VarIs _ (Ident nm) e -> (nm, Just e)
desugarConArgs :: ConArgs' Loc -> (Located Name,[Located Name])
desugarConArgs = (id *** reverse) . go
  where go = \case
          CANil cloc (UIdent con) -> ((con,cloc),[])
          --arg's loc will be the same as cloc... I need an Ident wrapper
          --to get its actual location.
          CACons aloc ca (Ident arg) -> (id *** ((arg,aloc):)) $ go ca

--Frustrating: E.Abs' hasPosition class returns BNFC'Position instead of the
--a in CST_TyCon' a. hasPosition can be generalized simply by adding ' to the
--end of each CST_TyCon and using the same definition, so at least the 200
--lines of boilerplate will be easy to write (but a headache to maintain as
--I update the AST).
--Possible black magic solution to avoid the maintenance: use unsafeCoerce
--to coerce hasPosition to f a -> a. I'd still need an empty instance for
--each qualifying type.
--class HasPosition (f BNFC'Position) => HasPosition f?
class HasPosition f where
  hasPosition :: f a -> a

instance HasPosition M' where
  hasPosition = \case
    Module p _ -> p

instance HasPosition D' where
  hasPosition = \case
    Default p _ _ -> p
    Defun p _ _ _ -> p
    Instance p _ _ _ _ -> p
    TySig p _ _ -> p
    KindSig p _ _ -> p
    TySyn p _ _ -> p
    Import p _ -> p
    Global p _ _ -> p
    Data p _ _ -> p
    Tag p _ _ _ -> p

instance HasPosition ConArgs' where
  hasPosition = \case
    CANil p _ -> p
    CACons p _ _ -> p

instance HasPosition ModuleName' where
  hasPosition = \case
    MNil p _ -> p
    MCons p _ _ -> p

instance HasPosition GlobalRegion' where
  hasPosition = \case
    Memory p -> p
    Storage p -> p
    TStorage p -> p
    Code p -> p

instance HasPosition DataRHS' where
  hasPosition = \case
    Boxed p _ _ -> p
    Unboxed p _ -> p

instance HasPosition UnboxedRHS' where
  hasPosition = \case
    URHS p _ -> p

instance HasPosition DataCon' where
  hasPosition = \case
    DCArgs p _ -> p
    DCRecord p _ _ -> p

instance HasPosition DCA' where
  hasPosition = \case
    DCANil p _ -> p
    DCACons p _ _ -> p

instance HasPosition RecordField' where
  hasPosition = \case
    RF p _ _ -> p

instance HasPosition ConTag' where
  hasPosition = \case
    ConTag p _ _ -> p

instance HasPosition S' where
  hasPosition = \case
    SE p _ -> p
    If p _ _ _ -> p
    While p _ _ -> p
    Return p _ -> p
    Do p _ -> p
    Case p _ _ -> p
    Break p -> p
    Continue p -> p
    For p _ _ _ _ -> p
    Declare p _ -> p

instance HasPosition CASE' where
  hasPosition = \case
    C p _ _ -> p

instance HasPosition VarBind' where
  hasPosition = \case
    JustVar p _ -> p
    VarIs p _ _ -> p

instance HasPosition E' where
  hasPosition = \case
    EmptyTuple p -> p
    Tuple p _ _ -> p
    HexInt p _ -> p
    Int p _ -> p
    Var p _ -> p
    String p _ -> p
    ConRecord p _ _ -> p
    Con p _ -> p
    Wild p -> p
    PlusPlusPost p _ -> p
    MinusMinusPost p _ -> p
    Index p _ _ -> p
    Dot p _ _ -> p
    Bang p _ _ -> p
    Arrow p _ _ -> p
    App p _ _ -> p
    PlusPlusPre p _ -> p
    MinusMinusPre p _ -> p
    Negate p _ -> p
    Not p _ -> p
    BitwiseNot p _ -> p
    Deref p _ -> p
    AddressOf p _ -> p
    Mul p _ _ -> p
    Div p _ _ -> p
    Mod p _ _ -> p
    Plus p _ _ -> p
    Minus p _ _ -> p
    Shl p _ _ -> p
    Shr p _ _ -> p
    MyLT p _ _ -> p
    LTE p _ _ -> p
    MyGT p _ _ -> p
    GTE p _ _ -> p
    Eq p _ _ -> p
    NEq p _ _ -> p
    BitwiseAnd p _ _ -> p
    BitwiseXor p _ _ -> p
    BitwiseOr p _ _ -> p
    And p _ _ -> p
    Or p _ _ -> p
    Assign p _ _ _ -> p
    TypeAnnot p _ _ -> p

instance HasPosition EField' where
  hasPosition = \case
    EField p _ _ -> p

instance HasPosition AOp' where
  hasPosition = \case
    EqEq p -> p
    PlusEq p -> p
    MinusEq p -> p
    MulEq p -> p
    DivEq p -> p
    ModEq p -> p
    ShlEq p -> p
    ShrEq p -> p
    AndEq p -> p
    XorEq p -> p
    OrEq p -> p

instance HasPosition T' where
  hasPosition = \case
    TArrow p _ _ -> p
    TVar p _ -> p
    TNat p _ -> p
    TCon p _ -> p
    TEmptyTup p -> p
    TTup p _ _ -> p
    TApp p _ _ -> p
    TArray p _ _ -> p
