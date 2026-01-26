{-# LANGUAGE DeriveDataTypeable #-} --for generic global subst
module Structured.DTs where

--The DTs of the structured IR to which C is converted before Core conversion.
--Its purpose is to clarify the (stack) scope at every basic block and split
--exprs into explicit sequences of bind statements.

import AST.DTs
import Const.Const
import Core.RestrictedCore (Var(..),Value(..), OpE(..), Const(..),
                            FunVar(..),BranchValue(..),
                            Scope(..))

import Data.Map (Map(..))
import Data.Set (Set(..))
import Data.Data (Data(..)) --for generic global subst
--A difference from the old structured IR: Structured uses type-tagged vars
--for everything.

--Problem: to use forward traversal (declarations rather than liveness) to
--determine scope, I need to capture that only one value escapes from exprs.
--Wrapping exprs in a block-like construct would seem natural... but need to
--spec which var(s) leak.
--Problem 2: lhses of binds may be a mix of new and already-bound vars
--(e.g. (x,env) := call f y)
--Always bind es to a new var.
--Solution: implicit push/pop?
--caseTag would then pop tag from the top; ifte would pop w
--Need to separate dataflow and stack effect...
--Explicitly mark scope :: [Var], then there's no need for E blocks.
--Each E pushes a new var; var x = e binds that var to x#n, then declares the
--new scope.
--Note scope really only matters at BB boundaries.

--A complete structured program, with sufficient information to generate a
--Core program.
data Structured = Structured {
  --defuns
  --includes $trueMain, which calls main() and then stop()s.
  sdefuns :: Map FunVar (BranchValue,[Stmt]),
  --pointers: globals and static values
  --TODO also include E for symbolic opt of *codeG
  sglobals :: Map Name (Region, T, Maybe Serialized),
  --DT tags, fields etc per monotype
  stagSchemes :: Map (Name, [T]) ([Name], TagScheme (E, Serialized)),
  sdtsInfo :: DTsInfo E,
  --sizeof info
  ssizeof :: Map (Name,[T]) Integer
  }
  deriving (Eq,Ord,Read,Show,Data)
--ifte : (s => Word:s) (s => s) (s => s) -> (s => s)
--while : (s => Word:s) (s => s) -> (s => s)
--case : (s => tag:struct:s) [s => s] -> (s => s)
--Invariant: if a Stmt has a scope, that scope = locals,$ret,stk
data Stmt = Value := OpE --a straight-line primop
          | Call Scope [Var] Var [Var] --scope, retval, f, x (but no ret cont)
          --The BB will need to be split across calls later!
          | Ifte Scope [Stmt] Var [Stmt] [Stmt]
          --Initial scope, expr, var to branch on, th, el
          | While Scope [Stmt] Var [Stmt]
          --Why are the cases a list rather than a map? Because we can't elide
          --redundant cases at this stage.
          --TODO change args; dropped for now
          -- | Case Scope [Stmt] [Var] ConstSet [(Const,[Stmt])] [Stmt]
          --Initial scope, (tag,expr), its vars, tag scheme, cases, default
          | Break Scope
          | Continue Scope
          | Return Scope [Var] --v1..vN
          --For debugging purposes; todo replace String with a richer DT
          | Comment String
  deriving (Eq,Ord,Read,Show,Data)
