{-# LANGUAGE TemplateHaskell #-} 
module Stdlib.ImplicitImports where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (runIO,lift)

--This module handles loading the EVMC modules which are implicitly imported
--into EVMC programs (currently just Prim and Prelude) into the Haskell
--compiler as if they were hardcoded.
--Storing primitive/standard datatypes and functions in EVMC files allows more
--ergonomic development of them and simplifies the compiler, allowing it to
--treat primitives and user code more uniformly.
--ImplicitImports does *not* do any parsing or desugaring of the EVMC modules,
--that's left to Compiler.

--Currently Prim.evmc depends on type synonyms in Prelude.evmc, so they must
--be imported as a unit... but in future NoImplicitPrelude support may be
--added to EVMC.

stdlibPrim :: String
stdlibPrim = $(runIO (readFile "Stdlib/Prim.evmc") >>= lift)
stdlibPrelude :: String
stdlibPrelude = $(runIO (readFile "Stdlib/Prelude.evmc") >>= lift)
