module TypeCheck.TC where

import Util ((?))
import AST.DTs (Module(..))
import TypeCheck.TySyn (substTySyns,TySynError())
import TypeCheck.KindCheck (kindCheck,KindCheckError())
import TypeCheck.TypeInfer (typeInfer,TypeInferError())
--A separate typechecking pass, disentangling it from IR codegen.
--That allows integer literals, tuples and structs to be overloaded.

--EVMC's type inference is weaker than Hindley-Milner: when typechecking an
--expr it has a desired type :: Maybe T.
--Exprs get a desired type when you know they must have a given type in its
--context, e.g. the argument in f x, the rhs in p = e, or the arg in Con arg.
--Note the desired type may include tyvars, which are treated as wildcards.
--There is no global unification; e : (a,a) will be treated the same as
--e : (a,b).
--Example:
--f x : ? --no desired type
--(a -> b) <- typecheck f : ?
--_ <- typecheck x : a
--The idea behind this "push-down type inference" is to enable overloaded
--exprs with a very simple inference algo, avoiding the complexity and global
--state of HM.
--The end result of type inference is that every subexpression is tagged with
--a TypeIs t with a monomorphic t.

--Stages:
--1)Type synonym substitution
--Failure modes: tycon not in scope, underapplied tysyn


--2)Kind check
--Ill-kinded types may occur in:
--defun tysigs, exprs, static data types, global types, datatype args.

--3)Type inference
--Function type inference:
--Global type info: funs, static, globals, dts, enums
--Local: return type, vars, localReturn stack
--Can the same algo be used for staticdata as well?
--Once static data has been typechecked, need to convert Con args in static
--data to anonymous staticdatatypes.

data TCError = TySynError TySynError
             | KindCheckError KindCheckError
             | TypeInferError TypeInferError
  deriving (Eq,Ord,Read,Show)
typecheck :: Module -> Either TCError Module
typecheck m = do
  m1 <- substTySyns m ? TySynError
  kindCheck m1 ? KindCheckError
  m2 <- typeInfer m1 ? TypeInferError
  return m2
