{-# LANGUAGE LambdaCase #-}
module TypeCheck.TypeInfer (typeInfer,TypeInferError()) where

import Util (complainIf)
import AST.DTs
import TypeCheck.TySyn (tyVars)

import Data.Map (Map(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

data TypeInferError = UnifyError UnifyError
                    | Placeholder String
  deriving (Eq,Ord,Read,Show)

--Relevant fields: defuns, static, global anonStaticCtr
--First, infer types of static data exprs, then allocate new staticdatatype
--decls for each nested constructor application.
--Second, infer for defuns.
--I can use the same algo for both... result: each subexpr tagged with its
--type.
--Sadly the desired type propagation means I can't use generic.
typeInfer :: Module -> Either TypeInferError Module
typeInfer = error "todo"

--Fixed:
--primfun types
--Those could be expressed using quantified patterns for more uniform
--treatment:
--copy (Ptr Memory a, Ptr r a, Int _ _) --note there are further constraints on
--r.
--Using the type template I could automate pushing down the desired type to
--the arguments... and support polyfuns later.
--Static context:
--fun, static, global, constructor, enum value types
--Global region is relevant due to &_
--Per-function:
--return, local return types (reader)
--local variables (state)

--What does &_ need to be applicable to?
-- &global
-- &pat = e => pat = *e
-- For now, don't add a &&_ pointer pattern escape
--Maybe &dt, but dt :: Ptr r Byte works just as well

--Three relevant types: S, E, Pat
data StaticInfo = SI {
  funs :: Map Name T,
  stats :: Map Name T,
  globs :: Map Name (T,T), --region, type
  cons :: Map Name T,
  enumvs :: Map Name T,
  returnType :: T,
  allocRegion :: Maybe T
  }
  deriving (Eq,Ord,Read,Show)
data TCS = TCS {
  localTypes :: Map Name T,
  localReturns :: [Maybe T],
  --Looks like I need some HM-like state after all for application...
  tyVarCtr :: Int
  }
  deriving (Eq,Ord,Read,Show)
type TC = ReaderT StaticInfo
          (StateT TCS
           (Except TypeInferError))

--Con arg means pushing down type templates is mandatory.
--Note: malloc() :: MPtr a would be a great use of pushdown polymorphism.
--Keeping global identity info would make it easier to lift the alloc ptr...

--Checks an expr is a valid static expr.
--Static expr ::=
--k, -k
--Vars: f, stat, EnumValue
-- &global
--Con arg
--{stat,...}, (stat,...)
validStatic :: StaticInfo -> E -> Bool
validStatic si = go
  where go = \case
          --Literals; string literals have already been lifted
          EInteger _ -> True
          PrimOp "negate" [EInteger _] -> True
          --f, stat, enumValue
          Var nm -> M.member nm $ M.unions [
            funs si,
            stats si,
            enumvs si
            ]
          -- &global
          PrimOp "&_" [Var g] -> M.member g $ globs si
          Con _ arg -> go arg
          EStruct fields ->
            all go $ map (\(_,_,e) -> e) fields

--New primfun: null(), returns 0 :: desired type

--Integer literals:
--k : Int s len => OK, truncate k
--k : ? => k : smallest uint(8*n) that fits k
--Vars:
--x : mt => if x is OOS scope then scope error, otherwise if mt = Just t
--require x's type is t
--Primops: complex, custom per primop.
--Struct expressions:
--struct : t[n] => require length is <=n, all fields anonymous; push down t
--into each field; left-pad with null() elements.
--struct : Struct fields => require struct's fields are a subset of fields;
--move named fields in struct to the appropriate position; default unspecified
--fields to null().
--An expr block could be used to preserve eval order of the fields.
--struct : ? => default to struct type.
--Dots e fs : t --get type of e : ?, require e.fs :: t
--Coerce t e : mt => Coerce t (e : ?) :: mt
--TypeIs t e : t' => require t' matches t; TypeIs t (e : t)
--Con arg : mt => unify mt with con rhs, then pass down required type template
--into arg. Check the resulting type matches.
--Ex cause of failure: data Pair a = MkPair (a,a)
--MkPair (a,b) will not error during pushdown phase because tyvars are treated
--as wildcards, but will fail on the final check.
--The return type depends on the region of the current alloc ptr...
--e @ (p,e) --check p is a Ptr mutableRegion Byte; locally use that as the
--alloc region.
--block {...} : mt => cons mt to local return types
--p = e : mt => decompose assignment first?
infer :: Maybe T -> E -> TC E
infer des e =
  case e of
    EInteger n
      | Just t@(Int s len) <- des ->
        return $ TypeIs t $ EInteger $ truncateInteger len n
      --If there is no constraint, default to uint(8*n)
      | noConstraint des -> return $ TypeIs (defaultIntType n) e
      | otherwise -> throwError $ Placeholder $ "Error in k: " ++ show des
    Var nm -> error "todo"
    --Need to unify b with des and pass it down to f...
    --Note I'll need to modify this if I add Closure a b
    f :$ x -> do
      tf <- quant (TyVar "a" :-> TyVar "b")
      let a :-> b = tf
      m <- localUnify des b
      f' <- infer (Just $ instantiate m tf) f
      let TypeIs (a' :-> b') _ = f'
      x' <- infer (Just $ instantiate m a) x
      let TypeIs a'' _ = x'
      complainIf (a'' /= a')
        $ Placeholder $ "App: " ++ show (a'',a')
      return $ TypeIs b' $ f' :$ x'
    PrimOp nm es -> error "todo"
    EStruct fields ->
      case des of
        Just (Struct fields') -> error "todo"
        Just (Array t len) -> error "todo"
        _ | noConstraint des -> error "todo"
        Just t' -> throwError $ Placeholder $ "Error in {...}: " ++ show t'
    Dots {} -> error "todo"
    Coerce t e -> do
      localUnify des t
      e' <- infer Nothing e
      return $ TypeIs t $ Coerce t e'
    TypeIs t e -> do
      localUnify des t
      e' <- infer (Just t) e
      return e'
    UnsafeCoerce t e -> do
      localUnify des t
      e' <- infer Nothing e
      return $ TypeIs t $ UnsafeCoerce t e'
    --If there is no alloc ptr, fail; otherwise region = r
    --Look up con's type, generate a new instance a -> b r with quant
    --Unify b r with des; push down a into arg
    --Return type: b r
    Con con arg -> error "todo"
    --Look up alloce's type; it must be a Ptr r Byte
    --If r is not a mutable region, fail.
    --locally set the alloc region to r
    e :@ (allocp,alloce) -> error "todo"
    BlockE ss -> error "todo"
    p := e -> error "todo"
--To typecheck assignment, I need to define how pattern-matching is decomposed
--into primitive operations var[.fields][ixs] = e
--_ = e => e
--{f: p} = e => p = e.f
--{...,p,...} = e
--if e is a struct => p = e#ix
--if e is a t[n] => p = e[ix]
--tup = e --check e is a tup, then convert tup to struct
-- *p
--I should perhaps eliminate Pat and use E instead... Index is currently
--E -> E -> Pat, but var[.fields][ixs] is a simple pattern.
    
--
inferS :: S -> TC S
inferS = error "todo"

--Allocates a type with new names based on a given type pattern
quant :: T -> TC T
quant t = do
  let vs = S.toList $ tyVars t
  vs2new <- M.fromList <$> mapM (\v -> do
                                    v' <- newTyVar
                                    return (v, TyVar v')) vs
  return $ instantiate vs2new t
newTyVar :: TC Name
newTyVar = do
  s <- get
  let n = tyVarCtr s
  put s{tyVarCtr = n + 1}
  return $ "$allocated" ++ show n
--Desired is either Nothing or a tyvar
noConstraint :: Maybe T -> Bool
noConstraint = \case
  Nothing -> True
  Just (TyVar{}) -> True
  _ -> False

--Truncates n to the range 0..2^bitLen-1
truncateInteger bitLen n =
  let modulus = 2 ^ bitLen
      n' = n `mod` modulus
  in if n' < 0 then n' + modulus else n'
--Smallest uint(8*m) that fits abs n, with minimum m = 1.
--Ex: -255 :: uint8, -256 :: uint16
defaultIntType :: Integer -> T
defaultIntType n = UInt $ 8 * (max 1 $ go $ abs n)
  where go 0 = 0
        go n = 1 + go (n `div` 256)

--Local unification (type pattern with pattern)
--Ex: a -> a, x -> Byte => {a: x, x: Byte}
--The rightmost pattern is implicitly quantified, so equal names on both sides
--are unrelated.
localUnify :: Maybe T -> T -> TC (Map Name T)
localUnify Nothing t = return M.empty
localUnify (Just des) t =
  case unify des  t of
    Left uerr -> throwError $ UnifyError uerr
    Right m -> return m

--unify is commutative modulo error message
--Invariant: if a = b, the lowest points to the highest (avoiding cycles)
unify :: T -> T -> Either UnifyError (Map Name T)
unify t1 t2 = snd <$> (runExcept $ runStateT (unifyM t1 t2) M.empty)
type Unify = StateT (Map Name T) (Except UnifyError)
--TODO replace Array constructor with a primitive tycon Type -> Nat -> Type
data UnifyError = TypeMismatch T T
                | FieldMismatch (Field ()) (Field ())
                | ArrayLenMismatch Integer Integer
  deriving (Eq,Ord,Read,Show)
unifyM :: T -> T -> Unify ()
unifyM t1 t2 = go (t1,t2)
  where go = \case
          (TyVar a, t) -> unifyVar a t
          (t, TyVar a) -> unifyVar a t
          (tf :$$ tx, tf' :$$ tx') -> do
            go (tf,tf')
            go (tx,tx')
          (Struct fields1, Struct fields2)
            | length fields1 == length fields2 ->
              mapM_ (\((p1,nm1,t1),(p2,nm2,t2)) ->
                       if (p1,nm1) /= (p2,nm2)
                       then throwError $
                       FieldMismatch (p1,nm1,()) (p2,nm2,())
                       else go (t1,t2)) $ zip fields1 fields2
          (Array t1 len1, Array t2 len2) ->
            if len1 /= len2
            then throwError $ ArrayLenMismatch len1 len2
            else go (t1,t2)
          (t1, t2) | t1 == t2 -> return ()
                   | otherwise -> throwError $ TypeMismatch t1 t2
unifyVar :: Name -> T -> Unify ()
unifyVar a (TyVar b)
  | a == b = return ()
  | a > b = unifyVar b (TyVar a)
unifyVar a t = do
  s <- get
  case M.lookup a s of
    Just tau -> unifyM tau t
    Nothing -> put $ M.insert a t s

--Note the map contains var -> var mappings which must be trampolined
--TODO rewrite using generic, normalize map first
instantiate :: Map Name T -> T -> T
instantiate m = go
  where go = \case
          TyVar nm
            | Just t <- M.lookup nm m -> go t
          tf :$$ tx -> go tf :$$ go tx
          Struct fields -> Struct $ map (\(pad,nm,t) -> (pad,nm,go t)) fields
          Array t len -> Array (go t) len
          t -> t

--Allocate new names for tyvars: $anon1..$anonN; those are syntactically
--guaranteed to be new.
quantify :: T -> T
quantify t =
  let vs = S.toList $ tyVars t
  in instantiate (M.fromList $
                  zip vs [TyVar $ "$anon" ++ show n | n <- [1..]]) t

--OK, I need to redesign the type inference from scratch (well, based on HM).
--Emit constraints while unifying; run other constraints, if any unsolved
--remain apply a relevant default (given by the vars in the constraint).
--Solving default: if var is unbound unify it with the default type (which may
--also be quantified and have defaults)
--Invariant: at the end of type inference (per function or staticData),
--all subexprs must be tagged with their monomorphic type.
--How to generalize to support template and quantified polyfuns?
--Add constraint => t syntax, make function type signatures optional.
--Template polymorphism: any use of a f :: c => t must either solve the
--constraint or propagate it.
--Assume all constraints have a runtime impact; only polymorphic functions with
--no constraints can be truly QP (placed once for all type instantiations).
--main :: () -> () has no constraint, forcing monomorphization.
--Could Closure implemented in EVMC be type-checked?
--data Closure a b = MkClosure {(a,c) -> b, SizedContainer c}
--getSized :: MPtr (SizedContainer a) -> a --a primitive
--apply clos a :=
-- case clos of
--   ps => return ps#0 &(*ps#1)
--Because the function pointer is fixed-size (regardless of whether you know
--(a,c) or b), the offset of &(*ps#1) should be knowable; then it should all
--typecheck.
--(struct :: s).field :: t => s has .field t, with known size and offset
--Support explicit dict datatypes?
--data KnownSizeof a where KSO :: Sizeof a => KnownSizeof a
--class Sizeof a where sizeof :: proxy a -> uint16
--I could default to primitives which take explicit dicts and then specialize
--them. deref :: (Dereferencable r, Sizeof a) => Ptr r a -> a
--Dicts are on stack (there's no implicit alloc), so they must be fixed-size
--class Dereferencable Memory where
-- primDerefMem :: (Ptr Memory a, Sizeof a) -> a
--Forget using padding info...
--Are multi-param typeclasses viable? What if anything makes them difficult?

--EInteger k :: Int s len, default s = Unsigned, default len = log256 k

--Var nm:
--unbound: scope error
--local: the tyvar allocated for nm
--defun, static, globl, enumValue: fixed

--f :$ x :: b
--f :: a -> b
--x :: a
--(from HM)

--EStruct fields
--This one's tricky... t st HasFields field2ts, default given by syntax
--A fixed set of constraints makes it easier.
--Constraint solving attempt:
--if t -> Struct fs, unify fields
--if t -> Array t len, check len, check all fields anon, unify each field type
--with t.

--e.fields :: a
--e :: t st HasField t fields a

--Coerce t e :: t => e :: tau
--ditto for unsafe coerce

--TypeIs t e :: t, e :: t

--Con arg :: dat r, r = allocR, arg :: lhs of Con
--I might be able to add GADTs and use them to implement closures later...

--e @ p => p :: Ptr r a

--Primops:
--arr[ix]
--Either arr :: t[len], ix :: Int s len
--or arr :: Ptr r a, ix :: Int s len, Dereferencable r, default r Memory
--Without polyfuns I don't need so many defaults...
