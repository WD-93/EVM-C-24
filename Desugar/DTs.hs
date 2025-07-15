{-# LANGUAGE  StandaloneDeriving, DeriveDataTypeable #-}
module Desugar.DTs (
  module E.Abs,
  module AST.DTs,
  module Data.Set,
  module Data.Map,
  module Data.Generics,
  DError(..),
  DInfo(..)
                   ) where

--This module is for storing the datatypes and tysyns essential to desugaring,
-- *not* for desugaring datatypes.

import E.Abs (Ident(..),UIdent(..))
import qualified E.Abs as P

--CST -> AST
import AST.DTs

import Data.Set (Set(..))
import Data.Map (Map(..))
import Data.Generics (Data(..),everything,mkQ,everywhere,mkT)

data DError = DuplicateDefun Name
            | BadDOrdering [P.D]
            | BadOpInType String
            | BadEInType P.E --catch-all error for desugarT
            | BadEInPat P.E --same for desugarP
            | BadDoInDesugarS [P.S]
            | AssignIsNotAnE P.E P.E --for now
            | DuplicateDeclsForName Name
            -- | CoerceMixedWithOps [Name]
            | GenericDError String
            -- | BitPaddingDeprecated
            --TODO remove bit padding from syntax and compiler
            | NegativeLengthArray Name Integer
            | TooLongArray Name Integer
            | StandaloneConstructorName String
            | DuplicateConstructors Name
            | BadPatternInCase P.E
            -- | MoreThan256EnumNamesInOneEnum
            -- ^A helpful message on the off chance whoever triggers it isn't
            --fuzzing for vulns
            -- | DuplicateEnumName Name Name
            | WildcardInExprContext
            | MalformedPattern P.E
            -- | DuplicateTySigs Name
            -- | DuplicateKindSigs Name
            | UnresolvedImport P.ModuleName
            -- | DuplicateTyCons Name
            | NonByteChar String
            | DuplicateFieldNames Name
            -- | DuplicateDefaults Name
            --TODO naming convention: Duplicate<singular>, not plural
            -- | DuplicateGlobal Name
            --Duplicate "Decl constructor" nm
            | Duplicate String Name
            | DefunInstanceOverlap (Set Name)
            --Datatype desugaring errors:
            -- | CreatedConConflictsWithExisting (ConInfo P.E) (ConInfo P.E)
            | TagDeclsofNonexistentDT (Set Name)
            | TagParamDTParamLengthMismatch Name [Name] [Name]
            | FreeVarInTagType Name T Name
            | ConMismatchInTagAndData Name (Set Name) (Set Name)
  deriving (Eq,Ord,Read,Show)

--Boilerplate instances... todo recommend BNFC does this
deriving instance Data P.D
deriving instance Data P.E
deriving instance Data P.S
deriving instance Data P.CASE
deriving instance Data P.VarBind
deriving instance Data P.Ident
deriving instance Data P.HexInteger
deriving instance Data P.EField
deriving instance Data UIdent
deriving instance Data P.AOp
deriving instance Data P.T
deriving instance Data P.ConArgs
deriving instance Data P.ModuleName
deriving instance Data P.GlobalRegion
deriving instance Data P.DataRHS
deriving instance Data P.UnboxedRHS
deriving instance Data P.DataCon
deriving instance Data P.DCA
deriving instance Data P.RecordField
deriving instance Data P.ConTag

--The module context required for desugaring SEP; passed as a parameter
--rather than as three parameterized functions. Boxed field status is
--represented as a map rather than (field -> Maybe boxedParentCon) to amortize
--the work of looking up status from DTInfo.
--1) the global set (used for g=>*g in P,E)
--2) boxed field status (used for bdt.field => *(...).fieldStructCon in E)
--3) a string numbering m (used for "str" => *($string++show m["str"]))
type DInfo = (Set Name, Map Name Name, Map String Int)
