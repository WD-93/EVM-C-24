{-# LANGUAGE LambdaCase #-}
module Compiler where

--Imports the modules for each step, handles running the pipeline

import Util ((?))

--String -> CST
import Parse (parseModule)
--Collecting modules
import E.Abs (UIdent(..))
import qualified E.Abs as P
import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Map (Map(..))
import qualified Data.Map as M
import System.Directory (doesPathExist,getCurrentDirectory)
import Control.Monad.Reader
import Control.Monad.State
--CST -> AST
import AST.DTs (Module(..))
import Desugar.Desugar (desugar, DError(..))
--Type checking
import TypeCheck.TC (typecheck, TCError(..))

data CompilerError = ParserError String
                   | DesugarError DError
                   | TypeCheckError TCError
                   {-
                   | SeqError SeqError
                   | IllFormedCFG Name [IR]
                   | AsmError String
                   | BytecodeError AsmError -}
  deriving (Eq,Ord,Read,Show)

--The compilation process is pure once you have the set of relevant modules...
--but collecting it requires parsing them.
collectModules :: [FilePath] -> [String] -> IO P.M
collectModules libpaths modname = do
  cwd <- getCurrentDirectory
  let searchPaths = libpaths ++ [cwd]
  ds <- evalStateT (runReaderT (loadModule modname) searchPaths) S.empty
  return $ P.Module ds

type ModuleLoader = ReaderT [FilePath] (StateT (Set [String]) IO)
--Loads a module and fills in its imports, recursively importing their
--imports.
loadModule :: [String] -> ModuleLoader [P.D]
loadModule modname = do
  explored <- get
  if S.member modname explored
    then return []
    else do
    put (S.insert modname explored)
    paths <- ask
    meim <- lift $ lift $ getModule paths modname
    case meim of
      Just (Right (P.Module ds)) ->
        concat <$> mapM (\case
                            P.Import mname ->
                              loadModule $ moduleName mname
                            d -> return [d]) ds
      _ -> error $ "getModule failed: " ++ show (paths,modname,meim)
--Returns Nothing if there is no module there, returns Just (Left (path,err)) if
--there is but there's a syntax error in the module at path.
getModule :: [FilePath] -> [String] ->
             IO (Maybe (Either (FilePath,String) P.M))
getModule paths modname = go paths
  where go [] = return Nothing
        go (path:paths) = do
          let modPath = path ++ "/" ++ fp
          b <- doesPathExist modPath
          if b
            then do
            str <- readFile modPath
            case parseModule str of
              Left err -> return $ Just $ Left (path,err)
              Right m -> return $ Just $ Right m
            else go paths
        fp = moduleName2Path modname ++ ".evmc"
moduleName :: P.ModuleName -> [String]
moduleName = \case
  P.MNil (UIdent nm) -> [nm]
  P.MCons (UIdent nm) rest -> nm : moduleName rest
moduleName2Path :: [String] -> FilePath
moduleName2Path = \case
  [nm] -> nm
  nm:nms -> nm ++ "/" ++ moduleName2Path nms

--No compiler params for now, just pass a module through the pipeline
{-
--The params to the pure compilation process... currently just the parsed
--module.
--Future: .exe or .o mode, opt level, verbosity
--Library paths could be a flag parameter, -l; it should be deleted
--after module loading.
--Command line: evmc [flags] modname
data CompilerParams = CompilerParams {
  cpModule :: P.M,
  cpFlags :: Flags
  }
  deriving (Eq,Ord,Read,Show)
type Flags = Map String String


--For debugging; skips module loading and uses no flags
pureParams :: String -> Either CompilerError CompilerParams
pureParams str = do
  m <- parseModule str ? ParserError
  return CompilerParams{cpModule = m, cpFlags = M.empty}
-}
pipeline2parse :: String -> Either CompilerError P.M
pipeline2parse str = parseModule str ? ParserError
pipeline2desugar :: String -> Either CompilerError Module
pipeline2desugar str = do
  m <- pipeline2parse str
  desugar m ? DesugarError
pipeline2typechecked str = do
  m <- pipeline2desugar str
  typecheck m ? TypeCheckError

{-
import DTs
import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.Trans.Except
import Control.Monad.State
import Text.Read (readMaybe)
import Data.List (sort)

--AST -> IR
import IR1 hiding (Ifte,While,Return)
--IR -> CFG (non-stack aware)
import CFG
--CFG2 -> Asm
import Stack
--Asm -> Bytecode
import Asm (Asm(..),AsmError(..),assemble,toExe)
import qualified Asm as A (Label(..))
import Data.Set (Set(..))
import qualified Data.Set as S
--For debugging:
import Pretty
--For file output
import Data.Char (intToDigit)
--For compile
import System.Directory (doesPathExist)
import Control.Monad.Reader

--Better compilation, allowing import declarations.
--import foo.bar.baz looks up path/foo/bar/baz.evmc, parses it, recursively
--imports its dependencies and splices in its decls into the importing
--module.
--Paths are searched in order: first each libpath, then cwd
--Repeated imports of the same module become noops.
--Produces a single executable, foo.bar.baz.evm.txt
--State: Set [String]
--Mistake: I didn't write my pipeline in terms of stageN -> stage(N+1)
--functions. Fixed now; TODO remove the redundant code in pipeline2*
compile :: [FilePath] -> FilePath -> [String] -> IO ()
compile libpaths cwd modname = do
  let searchPaths = libpaths ++ [cwd]
  ds <- evalStateT (runReaderT (loadModule modname) searchPaths) S.empty
  case (do
           irm <- fun2IR (P.Module ds)
           cfg <- fun2CFG irm
           cfg2 <- fun2CFG2 cfg
           asm <- fun2Asm cfg2
           fun2Bytecode asm
       )
    of
    Left err
      | AsmError str <- err -> do
          putStrLn "Asm error:"
          putStrLn str
      | let -> do
          putStrLn $ "Compiler error:"
          print err
    Right (undefinedLabels,bytecode)
      | undefinedLabels == S.empty -> do
          putStrLn $ "Compilation successful, writing to " ++ cwd
          writeFile (cwd ++ "/" ++ moduleName2Path modname ++ ".evm") $
            toHexString bytecode
      | let -> putStrLn $ "Undefined labels in asm: " ++ show undefinedLabels

  
--A simple compilation function; takes a file and produces a .evm.txt
--file containing the bytecode. Prints the error if compilation fails or if
--there are undefined labels.
--The bytecode produced by an EVMC module is not inherently a creation script;
--to deploy with create rather than setcode then code object values must be
--added to the language.
--Constructor parameters require an end pointer.

--Params: source file, dest path, output name
--
compileSingle :: FilePath -> FilePath -> String -> IO ()
compileSingle src dest nm = do
  str <- readFile src
  case pipeline2Bytecode str of
    Left err -> putStrLn $ "Compiler error: \n" ++ show err
    Right (s,bs)
      | s /= S.empty -> putStrLn $ "Undefined labels in program: " ++ show s
      | let -> do
          putStrLn $ "Compilation OK, writing to " ++ dest
          writeFile (dest ++ "/" ++ nm) $ toHexString bs
toHexString bs = "0x" ++ (do
                             b <- bs
                             [intToDigit $ b `div` 16,
                              intToDigit $ b `mod` 16])
        
--Now for some basic testing, using past failing cases
testModules :: [String]
testModules = [
  --The case below failed because of a bug in dfsR2L. Now it generates correct
  --but inefficient bytecode: 2 more swaps than necessary.
  "module {main:Int Unsigned 8->Int Unsigned 8;main x := return (1+x)}",
  "module {main:Int Unsigned 8->Int Unsigned 8;main x := main x}",
  "module {main:()->();main _ := main()}",
  "module {main:()->Int Unsigned 8;main _ := return 0}",
  "module {main:Int Unsigned 8->();main x := return ()}"
              ]

printIRM :: String -> IO ()
printIRM str =
  case pipeline2IR str of
    Right irm -> mapM_ putStrLn $ prettyIRM irm
    Left err -> putStrLn $ "Error: " ++ show err
--TODO dedup...
printCFG :: String -> IO ()
printCFG str =
  case pipeline2CFG str of
    Right (_,cfgm) -> mapM_ putStrLn $ showCFGM cfgm
    Left err -> putStrLn $ "Error: " ++ show err
--Doesn't display the version count or substitution maps.
printCFG2 :: String -> IO ()
printCFG2 str =
  case pipeline2CFG2 str of
    Right (_,cfg2m) -> mapM_ putStrLn $ showCFG2M cfg2m
    Left err -> putStrLn $ "Error: " ++ show err
printAsm str =
  case pipeline2Asm str of
    Right asms -> mapM_ (putStrLn . prettyAsm) asms
    Left err -> putStrLn $ "Error: " ++ show err

--Putting it all together (in progress):


--The string set is a warning of undefined labels; none should exist
pipeline2Bytecode :: String -> Either CompilerError (Set String, [Int])
pipeline2Bytecode str = do
  asm <- pipeline2Asm str
  objectFile <- assemble asm ? BytecodeError
  return $ toExe objectFile
fun2Bytecode :: [Asm] -> Either CompilerError (Set String, [Int])
fun2Bytecode asm = do
  objectFile <- assemble asm ? BytecodeError
  return $ toExe objectFile
  
pipeline2Asm :: String -> Either CompilerError [Asm]
pipeline2Asm str = do
  (stat,cfg2m) <- pipeline2CFG2 str
  funasm <- compile2asm cfg2m ? AsmError
  let statasm = do
        (label,(_t,labels_bytes)) <- M.toList stat
        PlaceLabel (A.LNamed label) :
          map (\case Left (lab,len) -> UseLabel len (A.LNamed lab)
                     Right byte -> Bytes [byte])
          labels_bytes
  return $ funasm ++ statasm
fun2Asm :: (Map Name Static, Map Name (Arity,(Label, CFG2))) ->
           Either CompilerError [Asm]
fun2Asm (stat,cfg2m) = do
  funasm <- compile2asm cfg2m ? AsmError
  let statasm = do
        (label,(_t,labels_bytes)) <- M.toList stat
        PlaceLabel (A.LNamed label) :
          map (\case Left (lab,len) -> UseLabel len (A.LNamed lab)
                     Right byte -> Bytes [byte])
          labels_bytes
  return $ funasm ++ statasm

pipeline2CFG2 :: String ->
                 Either CompilerError
                 (Map Name Static, Map Name (Arity,(Label, CFG2)))
pipeline2CFG2 str = do
  (stat,cfgm) <- pipeline2CFG str
  let cfg2m = M.map (\(arity,((lab,_live),cfgs)) ->
                          let cfg = labelSLCMap cfgs
                              (_,cfg') = processCFG (lab,cfg)
                          in (arity,(lab, opt2 lab cfg')))
                 cfgm
  return (stat,cfg2m)
fun2CFG2 :: (Map Name Static, Map Name (Arity,(LL,CFGS))) ->
            Either CompilerError
            (Map Name Static, Map Name (Arity,(Label, CFG2)))
fun2CFG2 (stat,cfgm) = do
  let cfg2m = M.map (\(arity,((lab,_live),cfgs)) ->
                          let cfg = labelSLCMap cfgs
                              (_,cfg') = processCFG (lab,cfg)
                          in (arity,(lab, opt2 lab cfg')))
                 cfgm
  return (stat,cfg2m)
--The CFG logic doesn't care about arity, so it can be passed through the
--CFG and CFG2 steps unchanged
--It doesn't care about statid data either, so I just pass it through
--unchanged.
pipeline2CFG :: String -> Either CompilerError
  (Map Name Static, Map Name (Arity,(LL,CFGS)))
pipeline2CFG str = do
  irm <- pipeline2IR str
  let ds = M.toList $ irDefuns irm
  fcfgs <- mapM (\(f,(arity,irs)) ->
                   case ir2cfg irs of
                     (Just ll, cfgs) -> return (f,(arity,(ll,cfgs)))
                     _ -> Left $ IllFormedCFG f irs) ds
  return (staticData irm, M.fromList fcfgs)
fun2CFG :: IRModule -> Either CompilerError
  (Map Name Static, Map Name (Arity,(LL,CFGS)))
fun2CFG irm = do
  let ds = M.toList $ irDefuns irm
  fcfgs <- mapM (\(f,(arity,irs)) ->
                   case ir2cfg irs of
                     (Just ll, cfgs) -> return (f,(arity,(ll,cfgs)))
                     _ -> Left $ IllFormedCFG f irs) ds
  return (staticData irm, M.fromList fcfgs)
  
--Compiles all the way to structured IR
pipeline2IR :: String -> Either CompilerError IRModule
pipeline2IR str = do
  m <- parseModule str ? ParserError
  mod <- desugar m ? DesugarError
  irmod <- seqModule mod ? SeqError
  return irmod
  --I need to generate IR for each function called from main
  --Seq only handles a single function's IR codegen
--fun2* is used to chain stages together without having to start from String
fun2IR :: P.M -> Either CompilerError IRModule
fun2IR m = do
  mod <- desugar m ? DesugarError
  irmod <- seqModule mod ? SeqError
  return irmod


-}
