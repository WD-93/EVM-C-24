{-# LANGUAGE PatternSynonyms, OverloadedStrings, LambdaCase,
DeriveDataTypeable #-}
module AST.DTs where

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except (Except(..),runExcept,throwError) --for unification
import Data.String (IsString(..))
import Data.Generics --for SYB

--For duplicatedShowT; TODO remove...
import Data.List (intercalate)

--AST, converted from BNFC CST in desugaring stage
type Name = String
data E = EInteger Integer
       --EString is no longer needed because lifting is done in desugar
       -- | EString String
       | Var Name --includes overloaded ops
       | E :$ E --Proper function application; excludes primops
       --Note && and || are not primops; they're desugared to block exprs
       | PrimOp Name [E] --primop/primfun application
       --The second Padding is alignment
       | EStruct [Field E]
       -- | E :. Name --struct field access
       -- | E :# Int --struct field access by index
       | Dots E [Either Name Int]
       --tuples are sugar for structs
       --Hard coercion: zero-pads or truncates e
       --Doesn't zero internal padding for now; coercing to a struct
       --is dangerous.
       | Coerce T E
       --Type declaration, not coercion; useful for overloaded exprs
       --(a,b,c), {a,b,c}, k
       | TypeIs T E
       --Unsafe(r) coercion: doesn't do any masking, so it's zero-cost but
       --can produce corrupt values on stack.
       | UnsafeCoerce T E
       -- *e becomes deref(e), so it doesn't need a dedicated constructor
       --Constructor application is substantially different from function
       --application...
       --I'll therefore add a new construct rather than reusing :$
       --The alloc ptr param is now given by @ (which handles entire expressions
       --rather than a single constructor), so constructors no longer need a
       --pattern parameter.
       | Con Name E
       --Statically specify the implicit alloc ptr parameter
       --Ex: Cons 1 (Cons 2 (Nil ())) @ memptr
       --The pattern parameter must be both a valid pattern and an expression
       -- :: a mutable byte ptr
       | E :@ (Pat,E)
       --Block expressions, which may contain control flow; can be used to
       --implement short-circuited combinators, ternary expressions and
       --inlining.
       --Exited via localReturn <level> e; if you reach the end without a
       --return a null value (all bits 0) is implicitly returned.
       -- <level> specifies how many nested block expressions to return out of;
       --the returned value is softCoerced to the type of the block it's
       --returning from.
       | BlockE [S]
       --Assignment moved to E
       | Pat := E
  deriving (Eq,Ord,Read,Show,Data)
--Tuples are word-padded structs with default field names;
--the default for structs is byte padding;
--currently there is no support for bitfields
data Padding = Byte | Word
  deriving (Eq,Ord,Read,Show,Data)
pad2Sz :: Num a => Padding -> a
pad2Sz = \case
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
pattern Type n = TyCon "Type" :$$ TyNat n
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
       --Invariant: n >= 0; no region specified because it's unboxed (!)
       | Array T Integer
  deriving (Eq,Ord,Read,Data)
--Making T show prettier by duplicating Pretty code...
--TODO move IR1's data decls here so it can import Pretty.hs without a cycle.
instance Show T where
  show = duplicatedShowT
duplicatedShowT = do
  let r = showT
      showT = duplicatedShowT
  \case
    UInt n -> "uint"++show n
    SInt n -> "int"++show n
    a :-> b -> "(" ++ r a ++ " -> " ++ r b ++ ")"
    TyCon nm -> nm
    TyVar nm -> nm
    --TODO reconcile with showT; add smarter paren emission
    tf :$$ tx -> r tf ++ " (" ++ r tx ++ ")"
    TyNat n -> show n
    tup | Just ts <- unTupleT tup ->
          "(" ++ intercalate ", " (map showT ts) ++ ")"
    Struct fields -> "{" ++ intercalate ", "
      (map duplicatedShowFieldT fields) ++ "}"
    Array t n -> "(" ++ r t ++ "[" ++ show n ++ "])"
duplicatedShowFieldT ((pad,al),mnm,t) =
  let p = case pad of
            Byte -> []
            Word -> ["pad word"]
      a = case al of
            Byte -> []
            Word -> ["align word"]
      n = case mnm of
            Nothing -> []
            Just nm -> [nm,":"]
  in unwords $ p ++ n ++ [duplicatedShowT t]

unTupleT :: T -> Maybe [T]
unTupleT = \case
  Struct padmnmts -> go padmnmts
  _ -> Nothing
  where go = \case
          [] -> Just []
          ((Word,Word),Nothing,t):padmnmts ->
            (t:) <$> go padmnmts
          _ -> Nothing

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
--Yup, useful for case.
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
data S = SE E --required because := has been moved to E
       | Return E
       | Ifte E S S
       | While E S
       | Case E [(Name,Pat,S)]
       | Block [S] --Standalone do, scopes locals
       | Break Int --break 0 ~ break in C; break n breaks out of n+1 loops
       | Continue Int --analogous
       | LocalReturn Int E --return out of n+1 nested block expressions
       
  deriving (Eq,Ord,Read,Show,Data)
--Determines whether an expr is a valid LHS for assignment
data Pat = PWild
         | PVar Name
         | PStruct [(Maybe Name, Pat)]
         | PTup [Pat] --rhs must have exactly that many fields and it
         --must be a tuple (word-padded with anonymous fields)
         | PDot Pat Name
         | PHash Pat Int
         | Deref E
         | PIndex E E --now required bc arr[ix] /=> *(arr + ix)
  deriving (Eq,Ord,Read,Show,Data)

--type Block = [S]
--type Program = [D]

--Output after desugaring phase:
data Module = Module {
  defuns :: Map Name (T,Pat,S),
  tysyns :: Syns,
  --T = Ptr Code a | somedatatype Code, i.e. the type is the type of the
  --name.
  --String expressions are lifted and become
  --newname => (Ptr Code Byte[len],{c1,c2,...})
  --Nested Con args and strings in static data are also lifted and
  --replaced with the new name.
  static :: Map Name (T,E),
  --the first T is a region: memory, t/storage
  globals :: [(Name,T,T)],
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
                            [Name]),--remaining params
  enums :: Map Name [Name],
  enumValues :: Map Name (Name,Int),
  --A counter for new names for static data decls $static<n>,
  --inserted as a hack to avoid having to change the desugar monad's type.
  anonStaticCtr :: Int
  }
  deriving (Eq,Ord,Read,Show)
type Syns = Map Name ([Name],T)

--Putting this utility function here to make it widely available.
--TODO update pkgs...
(!?) :: [a] -> Int -> Maybe a
xs !? n | n < 0 = Nothing
        | let = go xs n
                where go [] _ = Nothing
                      go (x:xs) n
                        | n == 0 = Just x
                        | let = go xs (n-1)
