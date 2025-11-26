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
            | BoxedTyConLacksKindSig Name
            | StructDTAlreadyGivenKindSig Name T
            --Final module check errors:
            | Clash String String (Set Name)
            | ClassFunctionsLackSignatures (Set Name)
            | TypeSignaturesLackBindings (Set Name)
            --Global errors:
            | BadGlobalRegion Name Region
            | MustNotHaveInitializer Name Region
            | CodeGlobalMustHaveInitializer Name
            --Field access errors
            | UndefinedFieldInDot Name
            --Constructor errors
            | ArrayAndStructTakeASyntacticTuple Name [P.E]
            | NoSuchCon Name
            | UnderappliedCon Name Int Int --arity, actual
            | OverappliedNonMkFun Name Int [E]
            | OverappliedPatternCon Name Int [Pat]
            | BadConInPattern P.E
            | FieldsDoNotMatchConInRecord Name (Set Name)
            | DuplicateFieldsInRecord Name (Map Name Int)
  deriving (Eq,Ord,Read,Show)

--Boilerplate instances... todo recommend BNFC does this
deriving instance Data a => Data (P.D' a)
deriving instance Data a => Data (P.E' a)
deriving instance Data a => Data (P.S' a)
deriving instance Data a => Data (P.CASE' a)
deriving instance Data a => Data (P.VarBind' a)
deriving instance Data a => Data (P.EField' a)
deriving instance Data a => Data (P.AOp' a)
deriving instance Data a => Data (P.T' a)
deriving instance Data a => Data (P.ConArgs' a)
deriving instance Data a => Data (P.ModuleName' a)
deriving instance Data a => Data (P.GlobalRegion' a)
deriving instance Data a => Data (P.DataRHS' a)
deriving instance Data a => Data (P.UnboxedRHS' a)
deriving instance Data a => Data (P.DataCon' a)
deriving instance Data a => Data (P.DCA' a)
deriving instance Data a => Data (P.RecordField' a)
deriving instance Data a => Data (P.ConTag' a)
--Token instances don't need a loc param
deriving instance Data P.Ident
deriving instance Data UIdent
deriving instance Data P.HexInteger

--The module context required for desugaring SEP; passed as a parameter
--rather than as three parameterized functions. Boxed field status is
--represented as a map rather than (field -> Maybe boxedParentCon) to amortize
--the work of looking up status from DTInfo.
--1) the global set (used for g=>*g in P,E)
--2) boxed field status (used for bdt.field => *(...).fieldStructCon in E)
--3) a string numbering m (used for "str" => *($string++show m["str"]))
--TODO change field => (boxed con) to field => boxed tycon instead.
--I could also desugar BCon {f: e} to
--ImplTyCon (allocValue (ImplBCon {implTyCon_f: e})).
--However, desugaring of BCon {f: p} = e must be deferred to the Core stage.
data DInfo = DInfo {
  diGlobalSet :: Set Name,
  diDTsInfo :: DTsInfo P.E, --used for field=>bcon, bcon=>fields
  diStringNumbering :: Map String Int
}
