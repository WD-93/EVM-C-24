module TypeCheck.TC where

import Util (complainIf,(?))
import AST.DTs (Module(..),Name)
import TypeCheck.TySyn (substTySyns,TySynError())
import TypeCheck.FIKS (fiks,FIKSError())
import TypeCheck.HM (tcModule,TCModuleError())

import qualified Data.Map as M
import qualified Data.Set as S

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

data TCError = DupParamsTo String [(Name,[Name])]
             | TySynError TySynError
             | FIKSError (Name,FIKSError)
             | TCModuleError TCModuleError
  deriving (Eq,Ord,Read,Show)
typecheck :: Module -> Either TCError Module
typecheck m = do
  --Check tysyn and datatype lhses are well-formed
  checkDupParams "tysyn" (tysyns m)
  checkDupParams "datatype" (datatypes m)
  m1 <- substTySyns m ? TySynError
  m2 <- fiks m1 ? FIKSError
  m3 <- tcModule m2 ? TCModuleError
  return m3
  where
    checkDupParams :: String -> M.Map Name ([Name],a) -> Either TCError ()
    checkDupParams decltype nm2args_m =
          let nm2args = M.toList $ M.map fst nm2args_m
              offenders = filter (\(nm,args) ->
                                    length args > S.size (S.fromList args))
                          nm2args
          in complainIf (offenders /= [])
             $ DupParamsTo decltype offenders
