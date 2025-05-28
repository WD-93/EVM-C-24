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
--E will now be redesigned to fit Hindley-Milner type inference; the
--distinction between primops and proper functions is handled in FIR
--(functional IR)
data E = EInteger Integer
       --includes primops, &&, ||, coerce, unsafeCoerce and constructors
       --(including tuples), *_, _[_] and .field
       | Var Name 
       | E :$ E --Function application, including primops
       --Type declaration, not coercion; useful for overloaded exprs
       | E ::: T
       --Inlining at the FIR level allows block exprs to be eliminated!
       --Assignment moved to E
       | Pat := E
       --Perhaps replace with a constructor for each length in future.
       | EArray [E]
       --Type application; not currently exposed by the syntax but essential
       --for performing Hindley-Milner transformation in the Module type
       --TyApp is only needed for functions, so it might as well just take a
       --Name.
       | TyApp Name [T]
       --Since functions are only defined at the top level (there are no
       --letrecs, lets or lambdas), I do not need TyLam Name E
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
tupleE [] = Var "Unit"
tupleE (e:es) = Var "Pair" :$ e :$ tupleE es
tupleF :: [e] -> [Field e]
tupleF = map (\x -> ((Word,Word),Nothing,x))
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
pattern Type = TyCon "Type"
pattern SInt n = Int "Signed" n
pattern UInt n = Int "Unsigned" n
pattern Int s n = "Int" :$$ s :$$ TyNat n
pattern a :-> b = "->" :$$ a :$$ b
infixr 5 :->
pattern Array n a = "Array" :$$ n :$$ a

pattern Unit = TyCon "Unit"
pattern Pair a b = TyCon "Pair" :$$ a :$$ b
--(a,b) desugars to Pair a (Pair b Nil), not Pair a b
pattern Tu2 a b = Pair a (Pair b Unit)
pattern Tu3 a b c = Pair a (Tu2 b c)
pattern Memory = TyCon "Memory"
pattern Storage = TyCon "Storage"
pattern TStorage = TyCon "TStorage"
pattern Calldata = TyCon "Calldata"
pattern Returndata = TyCon "Returndata"
pattern Code = TyCon "Code"
pattern Ptr r a = "Ptr" :$$ r :$$ a
type Field a = ((Padding,Padding), Maybe Name, a)
--Anonymous structs now removed; structs are instead in boxed and unboxed
--datatypes. Padding/alignment data can be in metadata describing the struct;
--it's not relevant to type checking.
--Array :: Nat -> Type -> Type is now a primtycon
data T = TyCon Name
       | TyVar Name --Only for data and tysyn type params initially
       | T :$$ T
       | TyNat Integer --for bitlens, array lens etc
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
    Array n t -> "(" ++ r t ++ "[" ++ r n ++ "])"
    t | Just ts <- unTupleT t ->
        "(" ++ intercalate ", " (map r ts) ++ ")"
    TyCon nm -> nm
    TyVar nm -> nm
    --TODO reconcile with showT; add smarter paren emission
    tf :$$ tx -> r tf ++ " (" ++ r tx ++ ")"
    TyNat n -> show n
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
unTupleT = go
  where
    go :: T -> Maybe [T]
    go = \case
      Pair a b -> (a :) <$> go b
      Unit -> Just []
      _ -> Nothing

unTupleE :: E -> Maybe [E]
unTupleE = go
  where go = \case
          Var "Pair" :$ e :$ es ->
            (e :) <$> go es
          Var "Unit" -> return []

{-
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
-}
--Now that I have kind signatures I don't need to hardcode kinds!
--EVMC does not support support declaring (->) or new kinds in source,
--so they must be hardcoded instead of in Prim.evmc.
--(->) is given the kind Type -> Type -> Type just so it can be put in the map,
--but it's in fact treated as polymorphic during kind check.
{-
hardcodedTyCons :: Map Name T
hardcodedTyCons = M.fromList $
  are "Type" "Type Region Signedness Nat" ++
  are "Signedness" "Signed Unsigned" ++
  are "Region" "Memory Storage TStorage Calldata Returndata Code" ++
  is ("Type" :-> "Type" :-> "Type") "->"
  where are t = map (\nm -> (nm,t)) . words
        is = are --English lesson of the day
-}
--Primitive type synonyms and functions now in Prim.evmc, so they don't need to
--be hardcoded.
  
--The kind check can't be done here, you need to defer it to IR.
tupleT :: [T] -> T
tupleT [] = Unit
tupleT (t:ts) = Pair t (tupleT ts) 

--No block expressions, so local return has been removed
data S = SE E --required because := has been moved to E
       | Return E
       | Ifte E S S
       | While E S
       | Case E [(Pat,S)]
       | Block [S] --Standalone do, scopes locals
       | Break
       | Continue
       --mandatory variable declaration; vars enter scope in textual order,
       --so var x = 1, y = x + x; is valid
       | Declare [(Name,E)] 
  deriving (Eq,Ord,Read,Show,Data)
--Determines whether an expr is a valid LHS for assignment
--Anonymous structs removed, so no struct patterns or #ix
--(a,b,c) desugars to (,) a ((,) b c); () desugars to PCon "()"
--Nice property: with mandatory var declarations, all valid patterns can be
--converted into exprs in scope (with _ => null())
-- &_ :: a -> Ptr r a (it may not be compilable even if well-typed ofc)
--Deref and PIndex are tricky: if their es are of the right form the
--pattern-matching can be optimized.
--Ex: *p (.field | unboxed array [ix]) = e =>
--writePtr (a series of transformations on p) e
type Pat = E
{-
data Pat = PWild
         | PVar Name
         | PCon Name [Pat]
         | Pat :. Name
         | Deref E
         | PIndex E E --now required bc arr[ix] /=> *(arr + ix)
         | Ampersand Pat -- &p = e => p = *e
  deriving (Eq,Ord,Read,Show,Data)
-}

--type Block = [S]
--type Program = [D]

--Output after desugaring phase:
data Module = Module {
  --Used for optional type signatures on funs, globals and statics;
  --decls order-independent to simplify desugar.
  --That also means you can put the API at the top of long files :)
  --LEVEL 1: types may only contain level-1 terms such as Memory, Word...
  tysigs :: Map Name T,
  --Allows the user to specify nonstandard kinds for datatypes; otherwise they
  --default to Type* -> Type for unboxed and Type* -> Region -> Type* -> Type
  --for boxed datatypes respectively.
  --It also allows non-value kinds and hierarchies thereof to be introduced;
  --an example would be Memory :: Region in Prim.evmc.
  --Current rules:
  --Any tycon of kind returning Type must have an associated
  --datatype definition (empty in the case of primitive types).
  --Otherwise, the only restriction is that the rhs must be in scope;
  --in particular, cycles are permitted.
  --All tycons are simply kinded; kind polymorphism is disallowed.
  --LEVEL 2: may only contain level-2 terms such as Region, Type...
  kindsigs :: Map Name T,
  --LEVEL 3: the top-level kinds, declared as Tycon : Kind.
  --Kind itself does not have a kind, so hierarchy depth is bounded.
  sorts :: Set Name,
  defuns :: Map Name (Pat,S),
  tysyns :: Syns,
  --E is restricted to static exprs (f, &global, static, k,
  --UnboxedCon staticArgs, BoxedCon staticArgs with region Code)
  --sv := e => sv has e's type, and can be implemented using either a push or
  --code pointer deref.
  --Strings become &sv, where sv := a byte array.
  --With HMTS a type signature is no longer mandatory; note the static value
  --is subject to the monomorphism restriction.
  static :: Map Name E,
  --the T is a region: memory, calldata, returndata, code, storage, tstorage
  --A type signature is no longer required; note globals are monomorphic.
  --The relative ordering of globals is arbitrary and users should not rely on
  --it.
  globals :: Map Name (Region,Maybe E),
  --Structs and enums have been merged into unboxed datatypes.
  --For both boxed and unboxed dts, datatypes with only one constructor can
  --have a 0-size tag; the rest are 1B.
  datatypes :: Map Name --TyCon
    ([Name], --params (0 or more, all Type)
     [ConDecl]), --Primitive datatypes have 0 constructors
  --Only boxed datatypes have entries; must be one of the params
  --Irrelevant to type inference
  datatypeRegions :: Map Name Name,
  --Tag info isn't needed for the TC stage, so it's added later.
  --The type of Cons is a -> List a -> List a, which is surprising since
  --EVMC functions are not closures. When compiling, underapplied constructors
  --are treated as an error in order to simplify the language
  --(if the programmer wishes to partially apply a constructor they may do
  --the wizardry themselves).
  constructors :: Map Name T,
  --Fields have their own namespace; during type inference e.foo becomes
  --Var ".foo" :$ e.
  --Each field has a type, constructor they deconstruct and index to the
  --constructor argument they return.
  fieldTypes :: Map Name T,
  fieldSpecs :: Map Name (Name,Int),
  --A counter for new names for lifting strings to static byte array decls,
  --inserted as a hack to avoid having to change the desugar monad's type.
  anonStaticCtr :: Int
  }
  deriving (Eq,Ord,Read,Show,Data)
type Syns = Map Name ([Name],T)
--todo add pad/alignment and tag value info
type ConDecl = (Name,Either [T] [(Name,T)])
--Unfortunate name conflict with the T patterns.
--Used to make bad global regions non-representable.
--It's the first two letters so I can convert it using read . take 2 . show
data Region = Me | St | TS | Ca | Re | Co
  deriving (Eq,Ord,Read,Show,Data)


--Putting this utility function here to make it widely available.
--TODO update pkgs...
(!?) :: [a] -> Int -> Maybe a
xs !? n | n < 0 = Nothing
        | let = go xs n
                where go [] _ = Nothing
                      go (x:xs) n
                        | n == 0 = Just x
                        | let = go xs (n-1)
