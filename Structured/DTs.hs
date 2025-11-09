module Structured.DTs where

--The DTs of the structured IR to which C is converted before Core conversion.
--Its purpose is to clarify the (stack) scope at every basic block and split
--exprs into explicit sequences of bind statements.

import AST.DTs
import Const.Serialize
import Core.RestrictedCore (Var(..),Value(..), OpE(..), Const(..),Pattern(..),
                            FunVar(..),ConstSet(..))

import Data.Map (Map(..))
import Data.Set (Set(..))
--A difference from the old structured IR: Structured uses type-tagged vars
--for everything. It's also not word-level.

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
  --includes $trueMain, which initializes memory globals and then calls main().
  sdefuns :: Map FunVar (Pattern,[Stmt]),
  --pointers: globals and static values
  sglobals :: Map Name T,
  sstatic :: Map Name Const, --code or mem global => its initializer
  --DT tags, fields etc per monotype
  stagSchemes :: Map (Name, [T]) ([Name], TagScheme (E, Serialized)),
  sdtsInfo :: DTsInfo E,
  --sizeof info
  ssizeof :: Map (Name,[T]) Integer
  }
  deriving (Eq,Ord,Read,Show)
--ifte : (Word:s) (s => s) (s => s) -> (s => s)
--while : (s => Word:s) (s => s) -> (s => s)
--case : (s => s) -> (tag:s => s)
data Stmt = Value := RHS
          | Ifte Var [Stmt] [Stmt]
          | While [Stmt] Var [Stmt]
          --Why are the cases a list rather than a map? Because we can't elide
          --redundant cases at this stage.
          | CaseTag [Var] ConstSet [(Const,[Stmt])] [Stmt]
          | Break
          | Continue
          | Return [Var]
          | Declare [Var]
          --declares the scope, defining what the subsequent code expects
          --Each non-Declare Stmt must be preceded by a Declare
  deriving (Eq,Ord,Read,Show)
data RHS = OpE OpE --a straight-line primop
         | Call Var [Var] --the BB will need to be split across this later!
  deriving (Eq,Ord,Read,Show)
