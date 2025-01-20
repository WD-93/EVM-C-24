{-# LANGUAGE PatternSynonyms, OverloadedStrings #-}
module DTs where

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.State
import Data.String (IsString(..))
--TODO split into DTs etc files
--TODO add BNFC syntax to repo
--Start: absolutely minimal complete pipeline

--AST, converted from BNFC CST in desugaring stage
type Name = String
data E = EInteger Integer
       | Var Name --includes overloaded ops
       | E :$ E
       | EStruct [(Padding, Maybe Name,E)] --tuples are sugar for structs
       -- | Coerce T E
  deriving (Eq,Ord,Read,Show)
--Tuples are word-padded structs with default field names;
--the default for structs is byte padding;
--bitfields are bitpadded
data Padding = BitPad | BytePad | WordPad
  deriving (Eq,Ord,Read,Show)
padModulo n sz = n * ((sz `div` n) + if (sz `rem` n) /= 0 then 1 else 0) 
tupleE :: [E] -> E
tupleE = EStruct . tupleF
tupleF :: [e] -> [(Padding,Maybe Name,e)]
tupleF = map (\x -> (WordPad,Nothing,x))
--Design change: generic structure rather than one constructor per type
instance IsString T where
  fromString = TyCon
instance Num T where
  fromInteger = TyNat
  (+) = undefined
  (-) = undefined
  (*) = undefined
  abs = undefined
  signum = undefined
pattern SInt n = Int "Signed" n
pattern UInt n = Int "Unsigned" n
pattern Int s n = "Int" :$$ s :$$ TyNat n
pattern a :-> b = "->" :$$ a :$$ b
--I should perhaps have separated structs and tuples after all...
pattern Pair a b = Struct [(WordPad,Nothing,a),(WordPad,Nothing,b)]
data T = TyCon Name
       | TyVar Name --Only for data and tysyn type params initially
       | T :$$ T
       | TyNat Integer --for bitlens, array lens etc
       | Struct [(Padding, Maybe Name, T)]
  deriving (Eq,Ord,Read,Show)
--Including kinds
primTyCons :: Set Name
primTyCons = S.fromList $
  words $
  "Type Region Signedness Nat " ++ --the kinds, except ->
  "Signed Unsigned " ++ --signedness
  "Memory Storage Calldata Returndata Code " ++ --region
  "Int Ptr -> " --the primitive types
primTySyns :: Map Name ([Name],T)
primTySyns = M.fromList [
  "Char" =: UInt 8,
  "Short" =: UInt 16,
  "Size_T" =: UInt 16,
  "Long" =: UInt 32,
  "Half" =: UInt 128, --why not?
  "Word" =: UInt 256,
  "UInt" =: ("Int" :$$ "Unsigned"),
  "SInt" =: ("Int" :$$ "Signed")
  ]
  where nm =: t = (nm,([],t))
--The kind check can't be done here, you need to defer it to IR.
tupleT = Struct . tupleF
{-
data Region = Memory
            | Calldata
            | Returndata
            | Storage
            | Code
  deriving (Eq,Ord,Read,Show)
-}
--TODO generic instance
data S = Pat := E
       | Return E
       | Ifte E Block Block
       | While E Block
  deriving (Eq,Ord,Read,Show)
--Determines whether an expr is a valid LHS for assignment
data Pat = PWild
         | PVar Name
         | PStruct [(Maybe Name, Pat)]
         | PTup [Pat] --rhs must have exactly that many fields and it
         --must be a tuple (word-padded with default names)
  deriving (Eq,Ord,Read,Show)
data D = Defun Name T Pat Block
  deriving (Eq,Ord,Read,Show)
type Block = [S]
type Program = [D]

--Output after desugaring phase:
data Module = Module {
  defuns :: Map Name D,
  tysyns :: Map Name ([Name],T)
  }
  deriving (Eq,Ord,Read,Show)

{-
--Type checking
--No datatypes for now, so no need for finiteness checks.
data TypeError = InFun Name TypeError
               | NonFunctionDefun Name T
  deriving (Eq,Ord,Read,Show)
tcModule :: Module -> Either TypeError ()
tcModule m = do
  let fundefs = M.toList $ defuns m
      fts = M.fromList $ map (\(nm,Defun _ t _ _) -> (nm,t)) fundefs
  mapM_ (tcFun fts) (defuns m)
tcFun :: Map Name T -> D -> Either TypeError ()
tcFun fts (Defun nm t args block) =
  case t of
    a :-> b -> do
      --First, match args to a
      undefined
    _ -> Left (NonFunctionDefun nm t)
type GlobalTypeInfo = GTI {funTypes :: Map Name T} --Just functions for now
type LocalTypeInfo = Map Name T --Just locals
type TCE = ReaderT GlobalTypeInfo (StateT LocalTypeInfo (Either TypeError))
runTCE :: TCE a ->
  GlobalTypeInfo ->
  LocalTypeInfo ->
  Either TypeError (a,LocalTypeInfo)
runTCE tce gti lti = runStateT (runReaderT tce gti) lti

puke :: TypeError -> TCE a
puke = lift . lift . Left
data NameInfo = IsUnbound
              | IsLocal T
              | IsFunction T
--Ah... when compiling I need to know the type of every subexpr
--I'll annotate the AST with types
-}

--Type consequences of pattern unification:
--patterns should be ~polymorphic, ignoring padding
--{foo: bar} = e --should match any struct where e.foo matches bar
--{x,y} = e => x = e<1>, y = e<2>
--Con x y z
--Disallow shadowing or assigning to functions

--New vars: any type matches
--Existing vars: only its type matches

--The type system is monomorphic, using the C trick to type literals;
--no type inference stage is required.
--However, separate type checking before compilation simplifies the
--codegen stage.
--Note adding type synonyms and (potentially recursive) data decls complicates
--sizeof.
--No need for newtype since the language is strict.
--First, no parameterized types other than fun and ptr.
--In TC, check datatypes are of finite size.
--data Con = Con t | ...
--Layout: if 1 constructor then layout of t; otherwise byte + byte padded
--max size of contents.
