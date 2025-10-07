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

       --Var now has type annotations, enabling one to get the type of a post-HM
       --E without additional context.
       | TypedVar (Maybe T) Name
       | E :$ E --Function application, including primops
       --Type declaration, not coercion; useful for overloaded exprs
       | E ::: T
       --Inlining at the FIR level allows block exprs to be eliminated!
       --Assignment moved to E
       | Pat := E
       --Perhaps replace with a constructor for each length in future.
       --EArray requires a type tag because empty arrays must be typed as well.
       | EArray (Maybe T) [E]
       --Type application; not currently exposed by the syntax but essential
       --for performing Hindley-Milner transformation in the Module type
       --TyApp is only needed for functions, so it might as well just take a
       --Name.
       | TyApp Name [T]
       --Since functions are only defined at the top level (there are no
       --letrecs, lets or lambdas), I do not need TyLam Name E
       -- | Let (Pat,E) E
       | CaseE E [(Pat,E)]
       --Making the lhs a Pat allows incremental decomposition of patterns
       --The Maybe E is for holding the parameterized op function after
       --Hindley-Milner.
       | OPAssign (Maybe E) Pat Op E
       | PPPre Pat
       | PPPost Pat
       | MMPre Pat
       | MMPost Pat
       -- ++ and -- are distinct from += because I will restrict + to
       --(a,a) -> a and use a separate indexPtr function for pointer
       --"addition". ++ and -- use inc/dec instead of +1/-1 to accomodate that.

       --Without lets in E, desugaring of Con {field: e} must be deferred
       --until after type inference and monomorphization.
       --Note eval order matters; unspecified fields are null()
       | ConRecord Name (Maybe [T]) [(Name,E)]
       --I'm adding back field access Dot in order to avoid having to
       --distinguish between ordinary function applications and .field
       --Note it needs a type annotation.
       | Dot E (Maybe [T]) Name
  deriving (Eq,Ord,Read,Show,Data)
--Isomorphic to P.AOp less Eq, which becomes :=
data Op = Plus
        | Minus
        | Mul
        | Div
        | Mod
        | Shl
        | Shr
        | And
        | Xor
        | Or
  deriving (Eq,Ord,Read,Show,Data)

{-
--Tuples are word-padded structs with default field names;
--the default for structs is byte padding;
--currently there is no support for bitfields
data Padding = Byte | Word
  deriving (Eq,Ord,Read,Show,Data)
pad2Sz :: Num a => Padding -> a
pad2Sz = \case
  Byte -> 8
  Word -> 256
-}
--padModulo n sz = n * ((sz `div` n) + if (sz `rem` n) /= 0 then 1 else 0)
n `roundedUpMod` m = m * ((if (n `mod` m) > 0
                          then 1
                          else 0) + (n `div` m))
--n `padWith` p = n `roundedUpMod` pad2Sz p

structT :: [T] -> T
structT [] = "Unit"
structT (t:ts) = Append t $ structT ts
structE :: [E] -> E
structE [] = ConRecord "Unit" Nothing []
structE (e:es) = ConRecord "Append" Nothing [("first",e),
                                             ("second", structE es)]
structP :: [Pat] -> Pat
structP [] = PCon "Unit" Nothing []
structP (p:ps) = PCon "Append" Nothing [("first",p),("second",structP ps)]

tupleE :: [E] -> E
tupleE [] = ConRecord "Unit" Nothing []
tupleE (e:es) = ConRecord "Pair" Nothing [("fst",e), ("snd",tupleE es)]
tupleP :: [Pat] -> Pat
tupleP [] = PCon "Unit" Nothing []
tupleP (p:ps) = PCon "Pair" Nothing [("fst",p),("snd",tupleP ps)]
--tupleF :: [e] -> [Field e]
--tupleF = map (\x -> ((Word,Word),Nothing,x))
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
--TyCon Fun is now used instead of -> to allow (->)'s structure to be defined
--in Prim.evmc
pattern a :-> b = "Fun" :$$ a :$$ b
infixr 5 :->
pattern Array n a = "Array" :$$ n :$$ a

pattern Unit = TyCon "Unit"
--Note: this is no longer tuple cons
pattern Pair a b = TyCon "Pair" :$$ a :$$ b
pattern Append a b = TyCon "Append" :$$ a :$$ b
pattern WordPad a = TyCon "WordPad" :$$ a
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
--type Field a = ((Padding,Padding), Maybe Name, a)
--Anonymous structs now removed; structs are instead in boxed and unboxed
--datatypes. Padding/alignment data can be in metadata describing the struct;
--it's not relevant to type checking.
--Array :: Nat -> Type -> Type is now a primtycon
data T = TyCon Name
       | TyVar Name --Only for data and tysyn type params initially
       | T :$$ T
       | TyNat Integer --for bitlens, array lens etc
       --forall (v : Type) . t
       --Used only in Core and only for v = stk (for now?)
       | TyForall Name T
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
    --TODO move pattern :-># to AST.DTs? 
    TyCon "->#" :$$ a :$$ b ->
      "(" ++ r a ++ " -># " ++ r b ++ ")"
    Array n t -> "(" ++ r t ++ "[" ++ r n ++ "])"
    t | Just ts <- unTupleT t ->
        "(" ++ intercalate ", " (map r ts) ++ ")"
    --A pair where b is not a syntactic tuple:
    Pair a b -> "(" ++ r a ++ " * " ++ r b ++ ")"
    TyCon nm -> nm
    TyVar nm -> nm
    --TODO reconcile with showT; add smarter paren emission
    tf :$$ tx -> r tf ++ " (" ++ r tx ++ ")"
    TyNat n -> show n
    TyForall nm t -> "forall " ++ nm ++ " . " ++ r t
{-
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
-}
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
--(a,b) => Append (WordPad a) (Append (WordPad b) Unit)
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

--Need to add a Maybe [T] tyannot list to every polymorphic op...
--TODO add a tyannot param to Module, STEP? Not for now.
data Pat = PWild (Maybe T) --not converted to new local until Core!
         --The atomic, infallible patterns
         | TypedPVar (Maybe T) Name
           --local only by type infer; global g is desugared to *g
         | Deref (Maybe [T]) E
         | PArray (Maybe T) [Pat] --Array (p1,p2,p3)
         --Converted to assignment of atomic pattern
         | PDot (Maybe [T]) Pat Name
         | PBang (Maybe [T]) Pat E
         --arr ! ix, distinct from ptr[ix] which is sugar
         --Con {field: p}, the only fallible pattern:
         --Repeated fields are a syntax error, despite Cons{hd:x,hd:y} being
         --useful.
         --Order matters because patterns may contain side-effecting exprs
         | PCon Name (Maybe [T]) [(Name,Pat)]
  deriving (Eq,Ord,Read,Show,Data)
pattern Var nm = TypedVar Nothing nm
pattern PVar nm = TypedPVar Nothing nm

pattern p :. field = PDot Nothing p field
pattern p :! ix = PBang Nothing p ix

--type Block = [S]
--type Program = [D]

--forall a b . a -> b becomes ([a,b],a -> b)
type Scheme = ([Name],T)
--Output after desugaring phase:
data Module = Module {
  --Used for optional type signatures on funs, globals and statics;
  --decls order-independent to simplify desugar.
  --That also means you can put the API at the top of long files :)
  --LEVEL 1: types may only contain level-1 terms such as Memory, Word...
  --Tysigs now also contain the canonical type param order; type params are
  --the a b c in forall a b c . t. Originally type params were in order of
  --appearance, but that led to Cons : a -> List r a -> List r a having param
  --order [a,r] whereas Nil : List r a had order [r,a]. Since the constructor
  --type params are used to determine the datatype params, that led to a bug
  --where Cons () Nil triggered the instantiation of the ill-kinded datatype
  --List () Memory.
  tysigs :: Map Name Scheme,
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
  kinds :: Set Name,
  --The default values for tyvars of that kind, e.g. Word for Type.
  --Must be monomorphic and match the given kind. Non-mandatory; a tyvar of
  --kind k with no default that remains unbound is an error.
  defaults :: Map Name T,
  --Left: an ordinary definition; Right: a set of instances
  --Note identical duplicate instances will be ignored.
  defuns :: Map Name (Either (Pat,S) (Set (T,Pat,S))),
  tysyns :: Syns,
  --A type signature is no longer required; note globals are monomorphic.
  --The relative ordering of globals is arbitrary and users should not rely on
  --it (TODO add layout region nms decl to fix it).
  --E is restricted to static exprs (f, &global, k, -k,
  --UnboxedCon staticArgs, BoxedCon staticArgs with region Code)
  --Strings become g where code g = a byte array.
  globals :: Map Name (Region,Maybe E),
  --All the datatype information merged into a single field; parameterized by
  --E because data and tag decls are desugared into DTInfo P.E before E
  --desugaring can be applied.
  dtsInfo :: DTsInfo E
  --Constructors are not given a function type because they're not functions.
  --When compiling, underapplied constructors
  --are treated as an error in order to simplify the language.
  --Fields have their own namespace; during type inference e.foo becomes
  --Var ".foo" :$ e.

  --A counter for new names for lifting strings to static byte array decls,
  --inserted as a hack to avoid having to change the desugar monad's type.
  --anonStaticCtr :: Int
  --No longer needed!
  }
  deriving (Eq,Ord,Read,Show,Data)
--All the info E desugaring and type checking need about datatypes.
--TyCon => params, tag type, canonical cons
--Con => boxed, TyCon, tag value, args: [field: T]
--field => boxed, Con
--Cons is ultimately desugared to ImplCons, so it doesn't belong in the
--constructor list of List.
--Relevant desugaring:
--e.f | (boxed,Con) <- info f =>
--(*e.fieldCon1).fStructCon
--Cons args => ImplCons (allocValue (StructCons args))
--Cons {f: e} => ImplCons (allocValue (StructCons {fStructCons: e}))
data DTsInfo e = DTsInfo {
  datatypes :: Map Name (DTInfo e),
  conInfo :: Map Name ConInfo,
  fieldInfo :: Map Name FieldInfo
                       }
  deriving (Eq,Ord,Read,Show,Data)
data DTInfo e = DTInfo {
  dtParams :: [Name],
  dtRegion :: Maybe Name,
  dtBoxed :: Bool,
  dtTagScheme :: TagScheme e,
  dtCanonicalCons :: [Name]
                     }
  deriving (Eq,Ord,Read,Show,Data)
{-
Default tag scheme:
DTs with 0-1 constructors don't even have a .tagTyCon field!
 User DT repr for 0-con type: the empty bytestring
 For 1-con type: the concatenation of the arguments' (bytestring) reprs.
 Specially treated primitives:
  Array len a: equivalent to a struct of len a's
  Int s len: len bytes
DTs with exactly 2 constructors are tagged with 0 or 1 : Byte, both because
jumpi is more efficient than jump tables for case on such types and to ensure
Bool is compatible with Boolean values returned by EVM primitives.
DTs with 3-16 constructors use 0,16,32.. : Byte as tags, allowing efficient
jump table dispatch by pushing the whole JT as a single word.
By using 15b jump addresses another constructor could be fit in, but that would
mess with linking of the JT since labels would cross byte boundaries.
DTs with >16 constructors can't use that trick; their repr is 0,1... in the
smallest UInt type that fits. That will be Byte or Short for any sane datatype,
but if the user wishes to define a datatype with a million constructors they
may.

Change: default tags are always UInts, never enums.
Information about possible values is still preserved.
-}
data TagScheme e = Nil    --DTs with 0-1 constructors, array, integer
                 | N1 Int
                   --DTs with 2 or >16 constructors; type is UInt <Int>
                 | N16    --DTs with 3-16 constructors; type is Byte
                 | Custom T (Map Name e)
                 -- ^ inline (unboxed) tags with arbitary, potentially
                 -- overlapping values. The values must be constants
                 -- (TODO test the compiler requires that).
  deriving (Eq,Ord,Read,Show,Data)
-- Each boxed DT points to an unboxed Impl<DT>; a DT is boxed iff
-- dtBoxed (datatypes (dtsInfo module)) == True.
-- Boxed datatypes inherit the tag scheme of their Impl type; note the
-- mappings in Custom refer to ImplCon rather than Con.
-- Iff Impl<DT>'s scheme is not Nil then DT has a tag field
-- .tagDT; bdt.tagDT desugars to *(bdt.unImplDT).tagImplDT.
-- Tag fields may not occur inside the {} brackets of a
-- record expression or pattern Con{...}; each datatype has
-- at most one tag field. TODO add that to test suite!

--Typecheck.HM.AddConsAndFieldsToTySigs uses dtTagType, which has been removed
--from the fields of DTInfo e... I'll add it as a helper here.
--Precondition: the tag scheme is not Nil.
dtTagType :: Show e => DTInfo e -> T
dtTagType dti =
  case dtTagScheme dti of
    Nil -> error $ "Compiler error: tag type of a datatype with no tag queried."
           ++ " DT Info: " ++ show dti
    N1 n -> UInt (fromIntegral n)
    N16 -> UInt 1
    Custom t _ -> t

data ConInfo = Con {
  conBoxed :: Bool,        --Whether the con is boxed (will be desugared away)
  conParent :: Name,       --parent datatype TyCon
  conFields :: [(Name,T)], --fields
  conRHS :: T              --rhs = TyCon params (cached)
  }
  deriving (Eq,Ord,Read,Show,Data)

data FieldInfo = IsTag {fiBoxed :: Bool,
                        fiParentTyCon :: Name 
                       }
               | IsNormal {fiBoxed :: Bool,
                           fiParentTyCon :: Name, --cached for bdt.field desugar
                           fiParentCon :: Name
                          }
  deriving (Eq,Ord,Read,Show,Data)

type Syns = Map Name ([Name],T)

--This is still required in Desugar.Desugar...
type ConDecl = (Name,[(Name,T)])

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
