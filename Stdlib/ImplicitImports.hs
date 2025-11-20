{-# LANGUAGE TemplateHaskell #-}
module Stdlib.ImplicitImports where

import Import

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (runIO,lift)
import Data.IORef

--This module handles loading the EVMC modules which are implicitly imported
--into EVMC programs (currently just Prim and Prelude) into the Haskell
--compiler as if they were hardcoded.
--Storing primitive/standard datatypes and functions in EVMC files allows more
--ergonomic development of them and simplifies the compiler, allowing it to
--treat primitives and user code more uniformly.
--A parse error in Stdlib will cause stdlib to = M.empty.
--Stdlib can now be split into as many files as necessary.

--Nice, with this it should be possible to ship a standalone exe.
stdlib :: Namespace
stdlib = $(runIO (do ior <- newIORef emptyCS{csPath=["Stdlib"]}
                     ei <- runLoader ior $ loadDir "Stdlib"
                     case ei of
                       Left err ->
                         putStrLn $ "Error when loading stdlib: " ++ show err
                       Right () -> return ()
                     csNamespace <$> readIORef ior)
            >>= lift)

--Currently Prim.evmc depends on type synonyms in Prelude.evmc, so they must
--be imported as a unit... but in future NoImplicitPrelude support may be
--added to EVMC.

{-
stdlibPrim :: String
stdlibPrim = $(runIO (readFile "Stdlib/Prim.evmc") >>= lift)
stdlibPrelude :: String
stdlibPrelude = $(runIO (readFile "Stdlib/Prelude.evmc") >>= lift)
-}
