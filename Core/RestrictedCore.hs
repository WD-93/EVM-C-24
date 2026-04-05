{-# LANGUAGE DeriveDataTypeable, PatternSynonyms, LambdaCase #-}
module Core.RestrictedCore where

import AST.DTs (T(..),Name(..),E(),tupleT)
import qualified AST.DTs as T (pattern Pair, pattern Unit)
import Const.Const
import Core.PrimTypes

import Data.Map (Map(..))
import Data.Set (Set(..))
import Data.Generics

--Core with a distinction between straight-line op exprs and branch exprs.
--Since Core is in CPS form, control is completely transferred on a branch
--(reflecting the reality of JUMP/JUMPI). In other words, all calls are tail
--calls and there's no such thing as returning from a call.
--There can therefore only be one branch in a Core expr, which consists of
--a set of letrec binds to constants (functions, globals etc) and a series
--of let binds to opEs.
--All opEs and branchEs are of the form (f x), where f is a primop and x is
--an ANF value consisting only of vars and tuples.
--Restricted Core closely resembles the CFG of the old design, with some key
--differences:
--Function calls take explicit continuations; continuations are typed
--first-class terms. A branch to a cont of the wrong type is an error.
--All branchEs take an explicit argument (usually the scope).

--Issue: ifte requires nested letrec-binding of the two branches' next
--While also requires letrec
--Why a Pattern rather than a Var in let? Because functions such as
--writePtr# return values you want to extract and treat individually.

-- $trueMain takes calldata, ext, sto etc and calls main
--Every mapping corresponds to a letrec; all letrecs are lifted
--Design Q: include all necessary state for compilation (less compiler flags)?
--Con: the state exists elsewhere already.
--Pro: transformations such as tree-shaking globals need a repr (in that case
--fs + gs + tags) to transform, which should ideally be kept consistent.

--Parameterizing by ops type (list pre-SSA, var => op map after) to allow
--SSA to return the same datatype:
type Core = Core_ [(Value,OpE)]
data Core_ ops = Core {
  --The basic blocks, including $trueMain
  coreDefuns :: Map FunVar (BranchValue, --lhs
                            FunRHS_ ops),
  --Core does not need to record the global set; they have already been erased
  --in Structured.
  --Region implicit in type
  --coreGlobals :: Map Name T,
  --Code global => its initializer
  coreStatic :: Map Name Const,
  --JTs are part of the control and dataflow graph during abstract
  --interpretation, so they need a lhs. That means that at least the arity
  --of that lhs must be recorded in order to allocate the right number of
  --abstract vars.
  coreJTs :: Map Name ((Int,  -- |word args|
                        Int), -- |state args|
                        [FunVar]
                      )
  }
  deriving (Eq,Ord,Read,Show)
--Rewrites: letrec merge, let merge, inline

type FunRHS = FunRHS_ [(Value,OpE)]
type FunRHS_ ops = (ops         --let ops
                   ,Branch      --in branch
                   )
type Scope = [Var] --Doesn't include the State vars

--Straight-line expressions
type OpE = (PrimOp,Value)
--The non-branching Core ops
--Final design: Const Constant | EVM op. No type params, they're implicit in
--argument and return vars. As with the old IR, the type of words is irrelevant
--to compilation (modulo padding info enabling opts).
--Side-effecting ops such as mstore implicitly consume state, requiring any
--readers be scheduled before it. However, Core needn't care about that.
data PrimOp = Push Serialized --k, f, g, Con{consts}; takes ()
            | Op Name --copy is dup ([x],[])
  deriving (Eq,Ord,Read,Show,Data)
--Branching expressions
--Since caseTag operates on constants rather than constructors, it's conceivable
--that the optimizer could recognize and deduplicate equivalent logic on
--different datatypes. Equivalent logic is especially easy to find for boxed
--datatypes, since the left-offset of the tag in the ImplDT doesn't matter.

--A jump is either a call, return or intraprocedural.
--For now Jumpi and case jumps are assumed to always be intraprocedural.
data Mode = Returning
          | Calling (Int,Int) --argument words, returned words
          | Intraprocedural
  deriving (Eq,Ord,Read,Show,Data)
data Branch =
  Jump Mode BranchValue
  --The cond and then branch are dynamic and part of the value.
  --The else branch is static (since JUMPI falls through).
  --To be able to easily estimate the size of the straight-line
  --skeleton for inlining + express whether the else cont is
  --inlined or not, the ops of the else branch are included in the
  --jumpi. If jumpi's scope is (cond*th*rest), the else branch's
  --scope is rest.
  --jumpi el (cond*th*scope,st) =
  -- if cond > 0
  -- then th (scope,st)
  -- else el (scope,st)

  --Changed else branch from (FunRHS_ ops) to FunVar, meaning else branches
  --can now be shared. That reflects real program behavior, e.g.
  --if cond then {stmt} else {} end, where stmt and the else branch both
  --continue to end.
  --That should mean I eliminate a bunch of trivial \scope -> jump f scope
  --else branches, but now compiling jumpis involves a nontrivial choice of
  --whether to copy or jump when the else branch is shared... and if you don't
  --copy, which branch should fall through. Note static jumps can also fall
  --through.
  | Jumpi FunVar BranchValue
  --The compilation of case depends on the range of possible values,
  --which is not determined by the type of the var being inspected
  --(many DTs have tag :: Byte but fewer than 256 constructors).
  --The range of possible values must either be inferred from
  --context or passed as an argument.
  --TODO change arguments; dropped for now
    {-
 | Case Var              --tag inspected
 ConstSet         --An upper bound on possible consts
 (Map Const FunVar) --cases
 FunVar           --default case
 BranchValue      --scope
    -}
  --Change: revert and return take off, len, state vars
  --They are equivalent to variants which take a bytestring
  --and persisted state vars in the case of return
  | Revert Value --off,len,mem
  --Bytestring# -> End
  | Return Value --off,len,(mem,ext,sto,tsto)
  --(Bytestring#,Ext,Sto,TSto) -> End
  --Stop deserves to be here as well
  | Stop Value --(ext,sto,tsto)
  deriving (Eq,Ord,Read,Show,Data)
--invalid is strictly worse than revert 0 0 (modulo code size), so it should
--never be generated.

--Redundant: TagScheme (E,Serialized) contains the same info
{-
data ConstSet = Consts [Const]
              --The sets of possible values for DTs with tag scheme N1 and N16
              --are represented compactly.
              --In future CSN1 may be used for case on integers.
              | CSN16 {csLo :: Integer,
                       csHi :: Integer
                      }
              | CSN1 {csSz :: Int,
                      csLo :: Integer,
                      csHi :: Integer
                     }
  deriving (Eq,Ord,Read,Show,Data)
-}
--Dynamic value names, as distinct from functions and globals.
data Var = Mono {nameOfVar :: Name, typeOfVar :: T}
  deriving (Eq,Ord,Read,Show,Data)

--Core functions have string labels...
type FunVar = Name
{-
--Note that now Core functions are polymorphic in stk (except in possible edge
--cases where they don't take stack at all) the name FMono is misleading;
--FPoly represents the equivalent of C functions, whose names take an additional
--typarams argument. TODO just tag all functions with their parent (Name,[T])?
data FunVar = FMono Name T --for auto-generated BBs
            | FPoly Name [T] T --for user-level functions
  deriving (Eq,Ord,Read,Show,Data)
-}
--Arg : Type -> State -> Argument
--State, Argument : Kind
--SUnit : State
--SPair : SElem -> State -> State
--Memory etc : SElem --prevents non-list tuples
--Tuple erasure ensures this repr is enough
--All Values are of kind Argument
type Value = ([Var],[Var])
--The argument passed to a branch may have a stack of form
--(x,y,z) (i.e. full stack is known) or x*y*z*stk (function is polymorphic in
--stk). To accomodate that it takes a Maybe Var parameter containing stk.
--When the full stack is known (e.g. in revert or inlining of main), you can
--ignore a suffix of the stack rather than pop it when stack scheduling.
type BranchValue = ([Var],Maybe Var,[Var])

--The concatenation of bytes and label slices. Labels have no concept of type,
--only size.
--Core function instantiation for a specific stk is just a dup/copy op.
--Consts are in normal form, i.e. they consist of a minimal number of sections.
--No adjacent bytestrings, no zero padding to the left in pushed words.
--All slices are of len > 0 and in range.
--Adjacent label slices are merged:
--(lab,from,len), (lab,from+len,len') => (lab,from,len+len')
--All pushed constants are <= 32B. You need to slice labels because they may
--be split across two or more pushes.
--Validity:
--All content bytes are 0 <= b < 256.
--Label slices are in the range of the given label.
type Const = Serialized
{-
newtype Const = MkConst [(Int, --byte length
                          Either (String,Int) --label name, slice offset
                          [Int] --bytes
                         )
                        ]
  deriving (Eq,Ord,Read,Show,Data)
-}

--Minimal env: (stackScope,($mem,$cd) :: Env)
--type Env = (Memory#,Calldata#)
--stackScope = (v1, v2 ... $ret)
--Why include $ret in the stackScope rather than in a separate top-level tuple
--index? Because sometimes it may not be passed.
--f : A -> B => Core f : Cont (a, Cont b)
--type Cont a = (a,Env) -> End#
--data End# = Revert# Bytestring# | Return# Bytestring#
--Return contains the persistent Env fields, but if I drop them for now then
--it contains only a bytestring.

--Env :: State
envT = sTupleT [MemoryState,
                StorageState,
                TStorageState,
                CalldataState,
                ReturndataState,
                ExtStateState,
                OtherState]
--New naming convention: each state var is named the lowercase version
--of its corresponding OpcodeInfo.State constructor
envV :: [Var]
envV = [Mono "$memory" MemoryState,
        Mono "$storage" StorageState,
        Mono "$tstorage" TStorageState,
        Mono "$calldata" CalldataState,
        Mono "$returndata" ReturndataState,
        Mono "$extstate" ExtStateState,
        Mono "$other" OtherState]

--The type of $ret for a C function : a -> b
--Fused knows the wordsize, so it passes it. 
returnContT :: Integer -> T -> T
returnContT wlen b =
  let bs = [W b (TyNat n) | n <- [1..wlen]]
  in Cont (foldr SPair (TyVar "stk") bs) envT
--Core functions, in which Env passing is made explicit:
--(->#) : Type -> Type -> Type
--data a -># b
--size: 2
--I now use stack-polymorphic Core functions!
--a -> b becomes forall stk . Cont (a * Cont (b*stk) * stk),
--where Cont t = (t,Env) -># End and (*) is Pair (right-associative).
--Note that's not a tupleT; a * b * c ... stk together forms one large tuple
--which is prepended to using (*). That allows arguments to be pushed
--incrementally and consumed off the stack later, fitting the behavior of
--efficient stack machine code.

--What's the point of having -># End# instead of an atomic Cont type?
--It's not strictly necessary, nor is using -># for straight-line ops
--(they're always fully applied, after all). The hope is it will simplify
--type checking (NB: done only for debugging purposes) and make lambda-calc-
--based rewrites and analysis easier.
--pattern a :-># b = TyCon "->#" :$$ a :$$ b




