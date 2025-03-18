{-# LANGUAGE PatternSynonyms, OverloadedStrings, LambdaCase #-}
module DTs where

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except (Except(..),runExcept,throwError) --for unification
import Data.String (IsString(..))
--TODO split into DTs etc files
--TODO add BNFC syntax to repo
--Start: absolutely minimal complete pipeline

--AST, converted from BNFC CST in desugaring stage
type Name = String
data E = EInteger Integer
       | EString String
       | Var Name --includes overloaded ops
       | E :$ E
       --The second Padding is alignment
       | EStruct [Field E]
       | E :. Name --struct field access
       | E :# Int --struct field access by index
       --tuples are sugar for structs
       --Hard coercion: zero-pads or truncates e
       --Doesn't zero internal padding for now; coercing to a struct
       --is dangerous.
       | Coerce T E
       -- *e becomes deref(e), so it doesn't need a dedicated constructor
       --Constructor application is substantially different from function
       --application and takes a pattern as its second argument...
       --I'll therefore add a new construct rather than reusing :$
       | Con Name E Pat
  deriving (Eq,Ord,Read,Show)
--Tuples are word-padded structs with default field names;
--the default for structs is byte padding;
--bitfields are bitpadded
data Padding = Bit | Byte | Word
  deriving (Eq,Ord,Read,Show)
pad2Sz :: Num a => Padding -> a
pad2Sz = \case
  Bit -> 1
  Byte -> 8
  Word -> 256
--padModulo n sz = n * ((sz `div` n) + if (sz `rem` n) /= 0 then 1 else 0)
n `roundedUpMod` m = m * ((if (n `mod` m) > 0
                          then 1
                          else 0) + (n `div` m))
n `padWith` p = n `roundedUpMod` pad2Sz p

tupleE :: [E] -> E
tupleE = EStruct . tupleF
tupleF :: [e] -> [Field e]
tupleF = map (\x -> ((Word,Word),Nothing,x))
--The byte-padded equivalent of tupleF; structE [a,b,c] => {a,b,c}
structF :: [e] -> [Field e]
structF = map (\x -> (((Byte,Byte),Nothing,x)))
structE = EStruct . structF
structT = Struct . structF
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
pattern Pair a b = Struct [((Word,Word),Nothing,a),
                           ((Word,Word),Nothing,b)]
pattern Triplet a b c = Struct [((Word,Word),Nothing,a),
                                ((Word,Word),Nothing,b),
                                ((Word,Word),Nothing,c)]
pattern Memory = TyCon "Memory"
pattern Storage = TyCon "Storage"
pattern TStorage = TyCon "TStorage"
pattern Calldata = TyCon "Calldata"
pattern Returndata = TyCon "Returndata"
pattern Code = TyCon "Code"
pattern Ptr r a = "Ptr" :$$ r :$$ a
type Field a = ((Padding,Padding), Maybe Name, a)
data T = TyCon Name
       | TyVar Name --Only for data and tysyn type params initially
       | T :$$ T
       | TyNat Integer --for bitlens, array lens etc
       | Struct [Field T]
  deriving (Eq,Ord,Read,Show)
--Unification is pretty fundamental, so might as well put it in here
--Left (mnm,t1,t2) => subtypes t1 and t2 failed to unify
--mnm = Just nm => unification was with nm, bound to t1
--Right m => a map from tyvar name to a T (of any kind)
--Precondition: only tpat contains tyvars; t is a monomorphic type
--To avoid confusion with full Hindley-Milner style unification, I'll call it
--bindT instead of unify.
bindT :: T -> T -> Either (Maybe Name,T,T) (Map Name T)
bindT tpat t = snd <$> runExcept (runStateT (bindTM tpat t) M.empty)
type Unify = StateT (Map Name T) (Except (Maybe Name,T,T))
--ExceptT (Maybe Name,T,T) (State (Map Name T))
bindTM :: T -> T -> Unify ()
bindTM tpat t = do
  let err = throwError (Nothing,tpat,t)
  case (tpat,t) of
    (TyVar nm, _) -> do
      s <- get
      case M.lookup nm s of
        Just t' ->
          if t == t'
          then return ()
          else throwError (Just nm,t,t')
        Nothing -> put (M.insert nm t s)
    (tf :$$ tx, tf' :$$ tx') -> do
      bindTM tf tf'
      bindTM tx tx'
    (Struct padnmts, Struct padnmts')
      | length padnmts /= length padnmts' -> err
      | let -> mapM_ (\((pad,mnm,t),(pad',mnm',t')) ->
                        if (pad,mnm) /= (pad',mnm')
                        then err
                        else bindTM t t') $ zip padnmts padnmts'
    _ -> if tpat == t
         then return ()
         else err
--Note this instantiation may leave free vars!
--Turns out I don't need it for alloc, but might be useful later.
instT :: Map Name T -> T -> T
instT m = go
  where go = \case
          TyVar nm
            | Just t <- M.lookup nm m -> t
            | let -> TyVar nm
          tf :$$ tx -> go tf :$$ go tx
          Struct padnmts -> Struct $ map (\(pad,nm,t) -> (pad,nm,go t)) padnmts
          t -> t

--Including kinds
primTyCons :: Set Name
primTyCons = S.fromList $
  words $
  "Type Region Signedness Nat " ++ --the kinds, except ->
  "Signed Unsigned " ++ --signedness
  "Memory Storage TStorage Calldata Returndata Code " ++ --region
  "Int Ptr -> " --the primitive types
primTySyns :: Map Name ([Name],T)
primTySyns = M.fromList [
  "Byte" =: UInt 8,
  "Char" =: UInt 8,
  "Short" =: UInt 16,
  "Size_T" =: UInt 16,
  "Long" =: UInt 32,
  "Half" =: UInt 128, --why not?
  "Word" =: UInt 256,
  "UInt" =: ("Int" :$$ "Unsigned"),
  "SInt" =: ("Int" :$$ "Signed"),
  ("Pair",(["a"],Pair (TyVar "a") (TyVar "a"))),
  "MPtr" =: ("Ptr" :$$ "Memory")
  ]
  where nm =: t = (nm,([],t))
--The kind check can't be done here, you need to defer it to IR.
tupleT :: [T] -> T
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
         | PDot Pat Name
         | PHash Pat Int
         | Deref E
  deriving (Eq,Ord,Read,Show)
data D = Defun Name T Pat Block
  deriving (Eq,Ord,Read,Show)
type Block = [S]
type Program = [D]

--Output after desugaring phase:
data Module = Module {
  defuns :: Map Name D,
  tysyns :: Map Name ([Name],T),
  static :: Map Name (T,[E]), --named staticData
  --the first T is a region: memory, t/storage
  --If the global is an array, the Maybe Int = Just arrayLen
  --Arrays of dynamic or indeterminate length are disallowed
  globals :: [(Name,T,T,Maybe Int)],
  --Used when compiling case
  datatypes :: Map Name --TyCon
               ([Name], --params (the first is region)
                [(Name, T)] --constructor; they all have exactly one param
               ),
  --Used when compiling allocation
  --Return type pattern is split into tycon, region param, rest to
  --make zero-param datatypes nonrepresentable and to simplify allocation
  constructors :: Map Name (Int,    --tag value
                            T,      --lhs type pattern
                            Name,   --tycon
                            Name,   --first param
                            [Name]) --remaining params
  }
  deriving (Eq,Ord,Read,Show)

--Putting this utility function here to make it widely available.
--TODO update pkgs...
(!?) :: [a] -> Int -> Maybe a
xs !? n | n < 0 = Nothing
        | let = go xs n
                where go [] _ = Nothing
                      go (x:xs) n
                        | n == 0 = Just x
                        | let = go xs (n-1)

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
