{-# LANGUAGE LambdaCase #-}
module Core.Flatten where

import AST.DTs
import AST.Util (rollTyApps)
import Core.RestrictedCore
import Core.PrimTypes
import Sizeof (Sizeof())
import Util ((?))

import Data.Map (Map(..))
import qualified Data.Map as M

{-
Core must be in tuple-free normal form:
The C function f : (A,B) -> C is converted to a Core function
f : forall stk . Cont (A * B * Cont (C * stk) Env * stk) Env
Values are represented as ([Var],[Var]), where fst is the stack and snd
is a list of state vars.
Tuples are flattened to a list of vars; zero-sized Types are omitted.

A function : () -> () then becomes
forall stk . Cont (Cont stk Env * stk) Env
Note: C function type -> Core function type conversion is not injective.

Tuples should be erased in:
1) Values (op lhs, rhs and branch arguments)
Note: the non-Value Var arguments in branches (th, el...) shouldn't pose a
problem because they're Conts, not tuples.
2) Core function types
...NOT in typarams, since the original structure of [x,y,z] needs to be
retained for [x,y,z].fst to be converted to the right contiguous subset of the
vars.

v :: Pair a b --should be converted to v.fst, v.snd and recursively flattened

-}

--flattenT erases tuples and eliminates zero-sized types; that means
--C function type -> Core type conversion is not injective!
--Because flatten must look up sizeof, it can't be :: T -> [T].
--sizeof lookup may fail, so flattenT must be fallible.
flattenT :: Map (Name,[T]) Integer -> T -> Either T [T]
flattenT sizeof = go
  where go = \case
          Unit -> return [] --redundant
          Pair a b -> (++) <$> go a <*> go b
          t -> do
            sz <- lookupSize sizeof t
            if sz == 0
              then return []
              else return [t]


lookupSize :: Sizeof -> T -> Either T Integer
lookupSize sizeof t
  | Cont {} <- t = return 2 --Core value types won't be in sizeof
  | let = case rollTyApps t of
            (TyCon tycon, ts) ->
              case M.lookup (tycon,ts) sizeof of
                Just sz -> return sz
                Nothing -> Left t
            _ -> Left t

--[] -> Unit
--[a,b,c] -> a*b*c
--Precondition for being a valid stack type: flattening has already been
--done, so none of the ts are tuples.
stackT :: [T] -> T
stackT [] = Unit
stackT ts = foldr1 Pair ts

--NB: a and b may not be closed over stk
fun2coreT :: Sizeof -> T -> T -> Either T T
fun2coreT sizeof a b =
  do as <- flattenT sizeof a
     bs <- flattenT sizeof b
     return $ TyForall "stk" $
       let stk = TyVar "stk" in
         Cont (stackT $ as ++ [Cont (stackT $ bs ++ [stk]) envT,
                               stk]) envT
--The monomorphic type of a return continuation expecting a b (free in stk).

flattenVars :: Sizeof -> [Var] -> Either T [Var]
flattenVars sizeof vs = concat <$> mapM go vs
  where go (Mono nm t) =
          case t of
            Unit -> return []
            Pair a b -> (++) <$> go (Mono (nm++".fst") a) <*>
                        go (Mono (nm++".snd") b)
            t -> do
              sz <- lookupSize sizeof t
              return $ if sz == 0
                       then []
                       else [Mono nm t]

--Every op takes and returns an Arg a s :: Argument.
--Its runtime value is represented as two Var lists, ([Var],[Var]).
--The Type a is flattened using flattenT; the State s is decomposed using
--flattenState into a list of SElem Ts.
data ArgReprError = TypeIsNotAnArg T
                  | FlattenTypeError T
                  | FlattenStateError T
  deriving (Eq,Ord,Read,Show)
argTypeToVars :: Sizeof -> T -> Either ArgReprError ([T],[T])
argTypeToVars sizeof t =
  case t of
    Arg a s -> do
      as <- flattenT sizeof a ? FlattenTypeError
      selems <- flattenState s ? FlattenStateError
      return (as,selems)
    _ -> Left $ TypeIsNotAnArg t

--Note: does not check the putative SElems are indeed SElems.
--Core will be kind and type-checked in debug mode if at all.
--Note if I later add a state tyvar which Core funs are polymorphic in
--(enabling a stack of SElem vars) this will incorrectly reject TyVar state
--as not a valid State.
flattenState :: T -> Either T [T]
flattenState = go
  where go = \case
          SUnit -> return []
          SPair se s -> (se:) <$> go s
          t -> Left t --Not a valid State
