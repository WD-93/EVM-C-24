{-# LANGUAGE LambdaCase #-}
module CLI where

import Import
import Stdlib.ImplicitImports (stdlib)
import Compiler (compile, CompilerError(..))
import DeclBucket (ModName())

import Data.IORef
import Data.List (intercalate)
import Data.Char (intToDigit)

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
no-stdlib --don't include stdlib in namespace; default is inclusion
load <modname> --add modname and its dependencies to namespace; found via path
load-dir <filepath> --load all .evmc files in dir and UIdent subdirs
A module name (e.g. Foo.Bar.Baz): compiles it to an EVM bytecode file
Foo.Bar.Baz.evm in the current working directory.

TODO flags:
dump-* --one for each stage, halt and dump result to file
code-size <nat> --bound code size
main-exec-intensity --tells the optimizer how much to weight exec cost vs
--code size
unsafe-case --disables validation in case clauses

-}
data Command = Help
             | AddPath FilePath
             | Flush
             | Load ModName
             | LoadDir FilePath
             | Compile ModName --syntax: Foo.Bar.Baz
  deriving (Eq,Ord,Read,Show)
evmc :: [Command] -> IO ()
evmc cmds = do
  ior <- newIORef emptyCS{csNamespace = stdlib}
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
        ,"load <modname> --add modname and its dependencies to namespace"
        ,"load-dir <filepath> --load all .evmc files in dir and UIdent subdirs"
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
