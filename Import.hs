{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving #-}
module Import where

import E.Abs hiding (P,E,S,T)
import AST.DTs (Name(..),Region(..))
import DeclBucket
import Parse (parseModule,isUIdent)
import Util --Errors

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad (forM_)
--File IO:
import System.Directory (listDirectory,doesFileExist,doesDirectoryExist)
import Data.List (intercalate)
import Control.Monad.Except
import Data.IORef
--import System.FilePath ((</>))

--Handles the module system.
--EVMC programs are divided into modules, each of which is in a separate .evmc
--file.
--Modules are parsed into a list of CST decls, which are then split into
--atomic decls and then merged into a DeclBucket.
sourceToBucket :: ModName -> String -> Either String --parse error
                  DeclBucket
sourceToBucket mnm str = do
  Module _loc ds <- parseModule str
  let lds = map (addModName mnm) ds
  return $ declsToBucket mnm lds
--Every module has a unique name Foo.Bar.Baz; a mapping from module names to
--DeclBuckets forms a Namespace.
type Namespace = Map ModName DeclBucket
--The IO phase of compilation collects relevant .evmc files into a namespace;
--the rest of the pipeline is pure.
--Given a namespace NS and a module M, the dependencies of M (including M
--itself) are determined by the transitive closure of imports.
--If an imported module M' is not in the namespace, compilation fails;
--duplicate imports are a noop.
--dependencies does not need to include nested deps from child contracts.
dependencies :: Namespace -> ModName ->
                Maybe --Nothing: the main module is missing
                (Set ModName,
                 [Located ModName] --missing imports
                )
dependencies ns mnm =
  case M.lookup mnm ns of
    Nothing -> Nothing
    Just db -> Just $ runWriter $
               execStateT (dependenciesM ns db) (S.singleton mnm)
type DepsM = StateT (Set ModName) (Writer [Located ModName])
dependenciesM :: Namespace -> DeclBucket -> DepsM ()
dependenciesM ns db = go db
  where
    go :: DeclBucket -> DepsM ()
    go db = forM_ (dbImports DoNotIncludeChildDeps db) go'
    go' lmnm@(mnm,_) = do
      b <- gets (S.member mnm)
      if b
        then return ()
        else case M.lookup mnm ns of
               --Note each located modname is unique
               Nothing -> tell [lmnm]
               Just db ->
                 modify (S.insert mnm) >> go db
--M and the dependencies ms are then merged into a single DeclBucket...
data CreateBucketError = MissingMainModule ModName
                       | MissingModules [Located ModName]
                       | CBEPanic ModName --the "impossible" has happened,
                       --the given dependency is not in the namespace
  deriving (Eq,Ord,Read,Show)
createBucket :: Namespace -> ModName -> Either CreateBucketError DeclBucket
createBucket ns mnm =
  case dependencies ns mnm of
    Nothing -> Left $ MissingMainModule mnm
    Just (present,missing)
      | null missing ->
        unionBuckets <$> mapM (\mnm ->
                                  case M.lookup mnm ns of
                                    Nothing -> Left $ CBEPanic mnm
                                    Just db -> return db) (S.toList present)
        --Would be nice if Set had a traversable instance
      | otherwise -> Left $ MissingModules missing
-- ...which is then checked for conflicting definitions.
--This is a simple check and doesn't catch everything:
--a tag decl for ImplTyCon that conflicts with the one which will be moved
--from TyCon will not be caught.
--PreModule is desugared to a Module; it's conflict-free, but contains CSTs
--instead of ASTs.
--Can I use a param to reuse the structure for Module, or must I restructure
--during desugaring? FW: param. For now, desugar to the existing Module
--structure.
type MNL a = Map Name (Located a)
data PreModule = PreModule {
  pmDefaults :: MNL T,
  pmTySigs :: MNL T,
  pmKindSigs :: MNL T,
  --The type of dynThings needs to be changed to accomodate instances.
  --Each instance has its own location.
  pmDynThings :: Map Name PMDynamicThing,
  pmStatThings :: MNL StaticThing,
  pmTagTypes :: MNL ([Located Name],T,[(Located Name, E)]),
  pmConTags :: MNL (Name,E), --parent tycon, tag expr
  pmConstructors :: MNL ConInfo,
  pmFields :: MNL FieldInfo
  }
  deriving (Eq,Ord,Read,Show)
data PMDynamicThing = PMDefun (Located (E,S))
                    | PMInstances (Set (Located (T,E,S)))
                    | PMGlobal (Located (Region, Maybe E))
                    | PMContract (Located DeclBucket) --(Located [DeclBucket.D])
  deriving (Eq,Ord,Read,Show)
type SL a = Set (Located a)
data ConflictingDecls = CDDefaults Name (SL T)
                      | CDTySigs Name (SL T)
                      | CDKindSigs Name (SL T)
                      | CDDynThings Name (SL DynamicThing)
                      | CDStatThings Name (SL StaticThing)
                      | CDTagTypes Name (SL ([Located Name],T,
                                             [(Located Name,E)]))
                      | CDConTags Name (SL (Name,E))
                      | CDConstructors Name (SL ConInfo)
                      | CDFields Name (SL FieldInfo)
  deriving (Eq,Ord,Read,Show)
deconflictBucket :: DeclBucket -> Either [ConflictingDecls] PreModule
deconflictBucket (DB dflts tsigs ksigs dts sts tts cts cons fs is ndeps) =
  runErrors $ PreModule <$>
  dc CDDefaults dflts <*>
  dc CDTySigs tsigs <*>
  dc CDKindSigs ksigs <*>
  dtproc <*>
  dc CDStatThings sts <*>
  dc CDTagTypes tts <*>
  dc CDConTags cts <*>
  dc CDConstructors cons <*>
  dc CDFields fs
  --Imports are dropped, they're no longer relevant
  where
    forEach f k2vs =
      M.fromList <$>
      flip traverse (M.toList k2vs) f
    --If any key has more than one element, throw the given error with a map
    --containing only the conflicting keys.
    dc :: Ord k => (k -> Set v -> err) -> Map k (Set v) -> Errors err (Map k v)
    dc err =
      forEach (\(k,vs) ->
                  case S.toList vs of
                    [] -> error "Panic! Impossible!"
                    [v] -> pure (k,v)
                    _ -> fling $ err k vs)
    --Dynamic thing processing:
    --If any key has more than one element, they must all be instances.
    --If the one element is an instance, convert it to a singleton instance
    --set.
    dtproc = forEach (\(k,vs) ->
                         case S.toList vs of
                           [] -> error "Panic! Impossible!"
                           [v] -> pure (k, toSingleton v)
                           vlist -> case mapM toLocInstance vlist of
                                      Nothing -> fling $ CDDynThings k vs
                                      Just lis -> pure (k, PMInstances $
                                                         S.fromList lis)
                     ) dts
    toSingleton (dt,loc) =
      case dt of
        DTDefun es -> PMDefun (es,loc)
        DTGlobal rme -> PMGlobal (rme,loc)
        DTInstance tes -> PMInstances $ S.singleton (tes,loc)
        DTContract ds -> PMContract (ds,loc)
    toLocInstance (dt,loc) =
      case dt of
        DTInstance tes -> return (tes,loc)
        _ -> Nothing

-- *******************************File IO:**************************************
--Why a newtype here and not for any of my other umpteen monads? Because I
--really want to enforce that the only IO actions it performs are checking
--module files exist and reading them.
newtype Loader err a = Loader (LoaderImpl err a)
  --Note I *don't* derive MonadState or MonadIO
  deriving (Functor,Applicative,Monad)
type LoaderImpl err a = StateT CompilerState (ExceptT err IO) a
--Doesn't modify the IORef unless the action succeeds.
runLoader :: IORef CompilerState -> Loader err a -> IO (Either err a)
runLoader csref (Loader m) = do
  cs <- readIORef csref
  ei_as <- runExceptT $ flip runStateT cs m
  case ei_as of
    Left err -> return $ Left err
    Right (a,cs') -> do
      writeIORef csref cs'
      return $ Right a
data CompilerState = CS {
  --Loaded modules.
  --Invariant: if M is in the namespace, all of its deps are as well.
  csNamespace :: Namespace,
  csPath :: [FilePath] --paths to find code; cwd checked last
  }
  deriving (Eq,Ord,Read,Show)
--Find the given Foo.Bar.Baz on the path, returning Nothing if it's missing.
--cwd is *not* implicitly included in path!
lookupModFile :: [FilePath] -> ModName -> IO (Maybe String)
lookupModFile path mnm = do
  dbgPrint $ "Looking for " ++ intercalate "." mnm
  go path
  where go = \case
          [] -> do
            dbgPrint "Didn't find it!"
            return Nothing
          fp:fps -> do
            let filepath = fp ++ "/" ++ modfp
            dbgPrint $ "Looking in " ++ filepath
            b <- doesFileExist filepath
            if b
              then do
              dbgPrint "Found it!"
              Just <$> readFile filepath
              else go fps
        modfp = intercalate "/" mnm ++ ".evmc"
--Used to drop stdlib
--initState can't be defined here, since ImplicitImports depends on Import
clearState :: Loader () ()
clearState = Loader $ put emptyCS
emptyCS = CS M.empty []
--O(n), but it's not like the user will have 1000 filepaths
--A noop if the path is already present
addPath :: FilePath -> Loader () ()
addPath fp = Loader $ do
  CS ns p <- get
  put $ CS ns $ go p
    where go = \case
            [] -> [fp]
            fp':fps
              | fp == fp' -> fp':fps
              | let -> fp':go fps
data LoadModuleError = ModuleMissing ModName
                     | ImportMissing (Located ModName)
                     | ModuleParseError ModName String
  deriving (Eq,Ord,Read,Show)
--load Foo.Bar.Baz first looks for Foo.Bar.Baz in the namespace, then
--in fp/Foo/Bar/Baz.evmc for each fp in the path. Errors if no module is found
--or the .evmc file fails to parse or to deconflict.
--Recursively loads dependencies.
loadModule :: ModName -> Loader LoadModuleError ()
loadModule mnm = Loader $ do
  ns <- gets csNamespace
  if M.member mnm ns
    then return () --It and its dependencies are already loaded.
    else do
    mstr <- lookupMod mnm
    case mstr of
      Nothing -> throwError $ ModuleMissing mnm
      Just str -> do
        db <- tryParseToBucket mnm str
        go mnm db
  where
    lookupMod :: ModName -> LoaderImpl LoadModuleError (Maybe String)
    lookupMod mnm = do
      path <- gets csPath
      liftIO $ lookupModFile path mnm
    tryParseToBucket :: ModName -> String ->
                        LoaderImpl LoadModuleError DeclBucket
    tryParseToBucket mnm str =
      case sourceToBucket mnm str of
        Left perr -> throwError $ ModuleParseError mnm perr
        Right db -> return db
    --Precondition: the mnm wasn't in ns before
    go :: ModName -> DeclBucket -> LoaderImpl LoadModuleError ()
    go mnm db = do
      modify (\cs->cs{csNamespace = M.insert mnm db $ csNamespace cs})
      mapM_ go' $ dbImports IncludeChildDeps db
    go' :: Located ModName -> LoaderImpl LoadModuleError ()
    go' (mnm,loc) = do
      b <- gets (M.member mnm . csNamespace)
      if b
        then return ()
        else do
        mstr <- lookupMod mnm
        case mstr of
          Nothing -> throwError $ ImportMissing (mnm,loc)
          Just str ->
            tryParseToBucket mnm str >>= go mnm

--Recursively enumerates all Foo/Bar/Baz.evmc files in the given directory,
--then loads them all. Used to load StdLib at Haskell compile time to enable
--it to be accessed purely. Doesn't follow .., but might get expensive if there
--are symlinks to huge dirs in the folder. Or if there's a recursive symlink!
--Conclusion: don't expose this in the CLI, just let the user use add-path.
--Inefficiency: I first traverse the dir to get the list of modnames, then I
--recompute the filepaths and traverse it again in the loadModule loop.
--I also u
--If modules with the same name are already in the namespace, modules in the
--dir will be ignored.
--I use ++ "/" ++ instead of System.FilePath.(</>)... that might cause
--portability issues.
loadDir :: FilePath -> Loader LoadModuleError ()
loadDir fp = do
  mnms <- Loader $ liftIO $ enumerateModNames fp
  Loader $ liftIO $ dbgPrint $ "Module names: " ++ show mnms
  mapM_ loadModule mnms
enumerateModNames :: FilePath -> IO [ModName]
enumerateModNames fp = map reverse <$> go [] fp
  where
    --nms is a stack of UIdent names.
    go :: [Name] -> FilePath -> IO [ModName]
    go nms fp = do
      contents <- listDirectory fp
      concat <$> mapM (go' nms fp) contents
    --file may be a dir or ordinary file
    --If it's a dir and a valid UIdent, recursively explore it.
    --If it's Mod.evmc, return ("Mod":nms). Mod must be a UIdent.
    go' nms fp filename =
      let fullPath = fp ++ "/"++filename
      in case () of
           _ | isUIdent filename ->  do
                 dbgPrint $ "Dir: " ++ filename
                 --It may be an explorable directory,
                 --but is certainly not a .evmc file.
                 b <- doesDirectoryExist fullPath
                 if b
                   then go (filename:nms) fullPath
                   else return []
             --Filenames are small... I'll just do a hacky Foo.evmc parse for
             --now.
             | let len = length filename
                   prefixlen = len-5, prefixlen > 0,
               let prefix = take (len - 5) filename
                   suffix = drop (len - 5) filename,
               isUIdent prefix, suffix == ".evmc"-> do
                 dbgPrint $ "Prog: " ++ filename
                 b <- doesFileExist fullPath
                 if b then dbgPrint "The file exists!" else return ()
                 return [prefix:nms | b]
             | let -> do
               dbgPrint $ "Ignore: " ++ filename
               return []

dbgFlag = False
dbgPrint str = if dbgFlag then putStrLn str else return ()
