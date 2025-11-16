{-# LANGUAGE LambdaCase #-}
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

--TODO include srcspans in parsed DTs instead of just tracking module.

import E.Abs
import AST.DTs (Name(..))

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S

type ModName = [Name] --Foo.Bar.Baz
type WithMod a = (a,ModName)
type TagInfo = (WithMod ([Name],T,[ConTag]))
type ConInfo = (WithMod (Name, --parent tycon
                         [(Name,T)] --Cons{hd:a,tl:List a}
                        )
               )
data DeclBucket = DB {
  dbDefaults :: Map Name (WithMod T),
  --tySigs should not include fields or cons
  dbTySigs :: Map Name (WithMod T),
  dbKindSigs :: Map Name (WithMod T),
  dbDynThings :: Map Name DynamicThing,
  dbStatThings :: Map Name StaticThing,
  dtTags :: Map Name TagInfo,
  dbConstructors :: Map Name ConInfo,
  dbImports :: Set ModName --no conflict possible, so no need for WithMod
  }
emptyBucket = DB e e e e 
--What possible conflicts are there?
--Tysigs and kind sigs form their own maps; for datatypes a kind sig is
--optional.
--Functions and globals
data DynamicThing = DTDefun (WithMod (E,S))
                  | DTInstances (Map T (WithMod (E,S)))
                  | DTGlobal (WithMod (GlobalRegion, Maybe E))
  deriving (Eq,Ord,Read,Show)
--Datatypes and tysyns
data StaticThing = STDatatype (WithMod ([Name], --typarams
                                        [Name], --constructors
                                        Maybe Name --r if boxed
                                     )
                              )
                 | STTysyn (WithMod ([Name],T))
  deriving (Eq,Ord,Read,Show)

--The ways decls can conflict:
--The conflicting thing which is already in the bucket is not included in the
--error. That allows errors from several bad decls to refer to the same
--element in the accumulated bucket when converting a module to a bucket.
--If both the new and old conflicting element were included, the old one would
--appear redundantly in each error.
data DeclConflict = DupDefault Name (WithMod T)
                  | DupTySig Name (WithMod T)
                  | DupKindSig Name (WithMod T)
                  | DupDynThing Name DynamicThing
                  | DupStatThing Name StaticThing
                  | DupTags Name TagInfo
                  | DupCon Name ConInfo
  deriving (Eq,Ord,Read,Show)

--Each conflict corresponds to an atomic decl, so no need for a DeclConflict
--type. Each ADecl has a key; in the case of dynthing instances form subkeys.
--Include conflicts in the DeclBucket!
--How to represent? Group by keys without assuming uniqueness.
--Instead of k => v, use k => Set v. Associate each ADecl with a UID so S.insert
--doesn't lose any. ID: ModName, nth decl, [nth con, [nth field]]
--Keep instances in a separate map. To verify a bucket, check
--instances ^ dynthings = {} and that each set is a singleton.
--API: D -> [ADecl], ADecl -> DeclBucket, DeclBucket -> DeclBucket -> DeclBucket
{-
Atomic decls:
default, tysig, kindsig
dynthing: defun | global | instance
statthing: data | tysyn

data TyCon params = Con1 {field1: t, ...} | ... [region r]
Decomposes to:
statthing: TyCon => params,cons
cons: Con => tycon,fts
fields: field => tag tycon | normal con
Desugar BDTs to two DTs here. Cost: less specific error messages.

tag TyCon params = t where {Con: e; ...}
Decomposes to:
tagtypes: TyCon => params, t
contags: Con => e

All other decls produce a single atomic decl
-}

--addDecl is the wrong abstraction: it makes it hard to
--report all conflicting constructors, since data implicitly declares
--multiple fields and constructors but addDecl must either completely fail
--or succeed.
--Solution: convert a single decl to a bucket, merge those.
--When merging buckets A and B, produce a maximal valid B' and put the rest of
--A in an error bucket.
--It could be worth splitting CST decls into a list of atomic decls first.
--(map ID, key, value)
--Problem: data TyCon as = cons implicitly declares .tagTyCon, but not its
--type. Con a b implicitly declares fields as well.
--Instance types are a subkey; it's simplest to start with a separate map for
--instances and then intersect with defuns and globals?
--Many maps is awkward... idea: a map k a => a. k would need to support Ord1
--(comparison of all k a).
--Many maps makes intersection cheaper...
--Why not have a separate instances map ((nm,t) => (e,s))? Because I'll need
--to restructure it to nm => (t => (e,s)) eventually anyway.
--To merge the dynThings map I need something like unionWithA.
declToBuckets :: ModName -> D -> [DeclBucket]
declToBuckets mnm = \case
  

--Decls are added one at a time when converting a module to a DeclBucket.
--If a module contains an internal conflict, you must still report the
--offending decl's module, so addDecl also needs a ModName parameter.
--Merging two modules into a bucket should have the same result whether you
--add a decl at a time or first convert each to a bucket and then merge the
--buckets. However, bucket merging is still worth supporting because it's
--more efficient.
--Since a data decl implicitly declares several vars, addDecl must also be
--able to throw multiple errors.
addDecl :: ModName -> D -> DeclBucket -> Either [DeclConflict] DeclBucket
addDecl mnm d db =
  case d of
    --tysig-like things
    Default (UIdent nm) t ->
      tryAdd DupDefault dbDefaults (\db x -> db{dbDefaults=x}) mnm nm t db
    TySig (Ident nm) t ->
      tryAdd DupTySig dbTySigs (\db x -> db{dbTySigs=x}) mnm nm t db
    KindSig (UIdent nm) t ->
      tryAdd DupKindSig dbKindSigs (\db x -> db{dbKindSigs=x}) mnm nm t db
    --Dynamic things: f, g
    Defun (Ident nm) e s ->
      tryAddDyn nm db $ DTDefun ((e,s),mnm)
    Instance (Ident nm) t e s ->
      tryAddDyn nm db $ DTInstances $ M.singleton t ((e,s),mnm)
    Global gr vb ->
      let (nm,me) = case vb of
                      JustVar (Ident nm) -> (nm,Nothing)
                      VarIs (Ident nm) e -> (nm,Just e)
      in tryAddDyn nm db $ DTGlobal ((gr,me),mnm)
    --Static things: datatypes, tysyns
    Data ca drhs ->
      let (nm,params) = unfoldConArgs ca
          (cons,
      tryAdd DupStatThing 
    TySyn ca t -> undefined
    --Datatype tag decls
    Tag ca t cts -> undefined
    --Imports (no conflict possible)
    Import modnm ->
      let mnm = unfoldModName modnm
      in return db{dbImports = S.insert mnm $ dbImports db}
  where
    tryAdd err getter setter mn nm thing db =
      let m = getter db
      in case M.lookup nm m of
           Nothing -> return $ setter db $ M.insert nm (thing,mn) m
           Just _ -> Left $ err nm (thing,mn)
    --instances with no syntactically equal types don't conflict;
    --everything else does
    tryAddDyn nm db dt =
      let m = dbDynThings db
      in case M.lookup nm m of
           Nothing -> return db{dbDynThings = M.insert nm dt m}
           Just dt' ->
             case (dt,dt') of
               --Note: sgtn is a singleton map, because it's from a single
               --instance.
               (DTInstances sgtn, DTInstances t2i)
                 | M.null $ M.intersection sgtn t2i ->
                   return db{dbDynThings = M.insert nm
                                           (DTInstances $ M.union sgtn t2i)
                                           m
                            }
               _ -> Left $ DupDynThing nm dt
    tryAddStat nm db st =
      let m = db
    unfoldModName = \case
      MNil (UIdent nm) -> [nm]
      MCons (UIdent nm) modnm -> nm : unfoldModName modnm
{-
data DynamicThing = DTDefun (WithMod (E,S))
                  | DTInstances (Map T (WithMod (E,S)))
                  | DTGlobal (WithMod (GlobalRegion, Maybe E))
  deriving (Eq,Ord,Read,Show)
-}

--What's the nicest way to report many errors when a single one stops execution?
--I could use the Validation applicative, but for my use case the simplest
--approach is the direct one.
mergeBuckets :: DeclBucket -> DeclBucket -> Errors DeclConflict DeclBucket
mergeBuckets = undefined

data Errors e a = L [e]
                | R a
  deriving (Eq,Ord,Read,Show)
instance Functor (Errors e) where
  fmap f (L es) = L es
  fmap f (R a) = R $ f a
instance Applicative (Errors e) where
  pure = R
  L xs <*> L ys = L $ xs ++ ys
  L xs <*> _ = L xs
  _ <*> L xs = L xs
  R f <*> R x = R $ f x
