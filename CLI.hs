{-# LANGUAGE LambdaCase #-}
module Main (main,evmc,
             --for debug:
             loadFrom,
             module Compiler
            ) where

import Import
import Stdlib.ImplicitImports (stdlib)
import Compiler (compile, CompilerError(..))
import DeclBucket (ModName())
import E.Par (pModuleName,myLexer)
import E.Abs (ModuleName'(..),UIdent(..))
--For debug:
import DeclBucket (DeclBucket(..))
import Util ((?))
import Compiler
import AST.DTs
import Opt.AI
import Opt.Opt --OptError, opt rules
import Core.RestrictedCore (Var(..)) --for varInfo nm fnm fms

import Data.IORef
import Data.List (intercalate)
import Data.Char (intToDigit)
import System.Environment (getArgs)

--For debug
import qualified Data.Map as M

--Defines the evmc CLI, which uses Import's Loader monad for setting up the
--module namespace and Compiler's compile function to convert modules to
--EVM bytecode.
--TODO pretty-print errors.
--Design: take commands all at once rather than interactively. Use a standard
--command-line argument parsing lib.
{-
Usage:
evmc command*
evmc accepts only .evmc files and produces .evm files.

Commands:
help --display usage
add-path <filepath> --add filepath to module search path
flush --flush namespace and path
A module name (e.g. Foo.Bar.Baz): compiles it to an EVM bytecode file
Foo.Bar.Baz.evm in the current working directory.

Removed:
load <modname> --add modname and its dependencies to namespace; found via path
load-dir <filepath> --load all .evmc files in dir and UIdent subdirs
Those are redundant since compiling module M implicitly loads it and its
dependencies, and the effect of loading depends only on the path.

TODO flags:
dump-* --one for each stage, halt and dump result to file
code-size <nat> --bound code size
main-exec-intensity --tells the optimizer how much to weight exec cost vs
--code size
unsafe-case --disables validation in case clauses

-}

main :: IO ()
main = do
  ws <- getArgs
  case parseArgs ws of
    Left err -> error $ "Command parse error: " ++ err
    Right cmds -> evmc cmds
parseArgs :: [String] -> Either String [Command]
parseArgs = go
  where
    go = \case
      [] -> return []
      "add-path":fp:rest -> (AddPath fp:) <$> go rest
      w:ws -> do
        cmd <- case w of
                 "help" -> return Help
                 "flush" -> return Flush
                 _ -> Compile <$> parseModName w
        cmds <- go ws
        return $ cmd:cmds
--Taken from the BNFC-generated parser
parseModName :: String -> Either String ModName
parseModName mnm =
  fmap go $ pModuleName $ myLexer mnm
  where
    go = \case
      MNil _ (UIdent nm) -> [nm]
      MCons _ (UIdent nm) rest -> nm : go rest

data Command = Help
             | AddPath FilePath
             | Flush
             | Load ModName
             | LoadDir FilePath
             | Compile ModName --syntax: Foo.Bar.Baz
  deriving (Eq,Ord,Read,Show)
evmc :: [Command] -> IO ()
evmc cmds = do
  --Quirk: cwd will be tried first, earlier paths shadow later ones.
  ior <- newIORef emptyCS{csNamespace = stdlib,
                          csPath = ["."]
                         }
  mapM_ (obey ior) cmds
  where
    obey ior = \case
      Help -> mapM_ putStrLn [
        "Usage:"
        ,"evmc command*"
        ,"evmc accepts only .evmc files and produces .evm files."
        ,""
        ,"Commands:"
        ,"help --display usage"
        ,"add-path <filepath> --add filepath to module search path"
        ,"flush --empty the namespace and path; flushes stdlib"
        ,"A module name (e.g. Foo.Bar.Baz): compiles it to an EVM bytecode file"
        ,"Foo.Bar.Baz.evm in the current working directory."
        ]
      AddPath fp -> do
        handleErr (runLoader ior $ addPath fp)
          (const "Error when adding path!?")
      Flush -> writeIORef ior emptyCS
      Load mnm -> do
        handleErr (runLoader ior $ loadModule mnm)
          (\err -> "Error in load " ++ showModName mnm ++ ": " ++ show err)
      LoadDir fp -> do
        handleErr (runLoader ior $ loadDir fp)
          (\err -> "Error in loadDir: " ++ show (fp,err))
      Compile mnm -> do
        --Load the module if it hasn't been loaded yet:
        obey ior (Load mnm)
        --Now it's in namespace
        namespace <- csNamespace <$> readIORef ior
        let pmnm = showModName mnm
        case compile namespace mnm of
          --TODO ppr and explain the compiler error
          Left compilerErr -> error $
            "Compiler error when compiling " ++ pmnm ++ ": " ++
            show compilerErr
          Right bs -> do
            --Forcing the structure in case there's an exception hidden
            --that would abort the file write partway through...
            let len = length bs
                invalid = any (\b -> b < 0 || b > 255) bs
            if len > 24000
              then error $ "Output of " ++ pmnm ++ " too long: " ++ show len
              else return ()
            if invalid
              then error $ "Output of " ++ pmnm ++ " contains non-bytes!"
              else return ()
            writeFile (pmnm ++ ".evm") $ serializeBytecode bs
    handleErr :: IO (Either err ()) -> (err -> String) -> IO ()
    handleErr io_ei f = do
      ei <- io_ei
      case ei of
        Left err -> error $ f err
        Right () -> return ()

--TODO deduplicate
showModName mnm = intercalate "." mnm
--Bytecode format: [255,255] => "0xffff"
--The 0x is redundant, but that's what hardhat recognizes.
--Precondition: the [Int] is a bytestring.
serializeBytecode :: [Int] -> String
serializeBytecode bs =
  "0x" ++ do
  b <- bs
  map intToDigit [b `div` 16, b `mod` 16]

--ABI.evmc currently (2026-07-25) triggers a SSA error, which is always a
--compiler error. To interactively debug the compiler using .evmc modules in
--another repo, I need a function for loading that code and pipeline functions
--that take a PreModule rather than a string.
--I compile to PreModule rather than DeclBucket in order to drop the module
--name and namespace.
--To keep Compiler.hs pure, I'll define the loading function here.
loadFrom :: [FilePath] -> --the path
            Bool -> --include stdlib in namespace?
            ModName -> --the module to compile
            IO (Either CompilerError PreModule)
loadFrom path include_stdlib mnm = do
  ior <- newIORef emptyCS{csNamespace =
                          if include_stdlib
                          then stdlib
                          else M.empty,
                          csPath = path
                         }
  --Load the module
  handleErr (runLoader ior $ loadModule mnm)
    (\err -> "Error in load " ++ showModName mnm ++ ": " ++ show err)
  --Now it's in namespace
  namespace <- csNamespace <$> readIORef ior
  return $ do
    db <- createBucket namespace mnm ? CreateBucketError
    pm <- deconflictBucket db ? ConflictingDecls
    --Contract decls converted to string globals:
    recursiveCompile namespace pm
    where
      handleErr :: IO (Either err ()) -> (err -> String) -> IO ()
      handleErr io_ei f = do
        ei <- io_ei
        case ei of
          Left err -> error $ f err
          Right () -> return ()

--Debug helper: get liveness and abstract value of a var with a given string
--name. Note each Var has a unique name.
varInfo :: String -> String -> FrozenModState -> FrozenAVar
varInfo nm fnm fms =
  let Just fi = M.lookup fnm $ funInfo fms
      av = snd $ head $ filter ((==nm).nameOfVar.fst) $ M.toList $ fiVars $
           fiBodyInfo fi
  in av
