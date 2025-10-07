{-# LANGUAGE DeriveDataTypeable, PatternSynonyms #-}
module Core.RestrictedCore where

import AST.DTs (T(..),Name(..),E(),tupleT)
import qualified AST.DTs as T (pattern Pair)

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

-- $trueMain takes calldata, ext, sto etc, sets up globals and calls main
--Every mapping corresponds to a letrec; all letrecs are lifted
--Design Q: include all necessary state for compilation (less compiler flags)?
--Con: the state exists elsewhere already.
--Pro: transformations such as tree-shaking globals need a repr (in that case
--fs + gs + tags) to transform, which should ideally be kept consistent.
data Core = Core {
  --The basic blocks, including $trueMain
  coreDefuns :: Map FunVar (Pattern, --lhs
                            [(Value,OpE)], --body, in SSA form
                             Branch),
  --Region implicit in type
  coreGlobals :: Map Name T,
  --Code global => its initializer
  --Mem global initialization is done in trueMain
  coreStatic :: Map Name Const
  }
--Rewrites: letrec merge, let merge, inline
          
--Straight-line expressions
type OpE = (PrimOp,Value)
--The non-branching Core ops
--Issue: should I make &(p->field) and &(*p!ix) explicit/opaque ops or
--implement them using unsafeAddPtr? Explicit helps preserve aliasing info.
data PrimOp = Const T Const --k, f, g, Con{consts}; takes ()
            | GetField [Field] --struct/arr => field
            | SetField [Field] --(f,struct/arr) => struct'/arr'
            | GetFieldPtr [Field]
            | MkCon Name [T] --(arg1,arg2,...) => Con{...}
            | Op Name [T] --includes id@[a]
  deriving (Eq,Ord,Read,Show,Data)
--A named field (static offset) or array index (dynamic offset)
--Why use a list of fields in the get/set primops?
data Field = NamedField Name [T] | ArrayIndex Var T
  deriving (Eq,Ord,Read,Show,Data)
--Branching expressions
--Since caseTag operates on constants rather than constructors, it's conceivable
--that the optimizer could recognize and deduplicate equivalent logic on
--different datatypes. Equivalent logic is especially easy to find for boxed
--datatypes, since the left-offset of the tag in the ImplDT doesn't matter.
data Branch = Jump Var Value
            | Jumpi Var Var Var Value
            --The compilation of case depends on the range of possible values,
            --which is not determined by the type of the var being inspected
            --(many DTs have tag :: Byte but fewer than 256 constructors).
            --The range of possible values must either be inferred from
            --context or passed as an argument.
            | Case Var              --tag inspected
                   ConstSet         --An upper bound on possible consts
                   (Map Const FunVar) --cases
                   FunVar           --default case
                   Value            --scope
            --Change: revert and return take off, len, state vars
            --They are equivalent to variants which take a bytestring
            --and persisted state vars in the case of return
            | Revert Var Var Var --off,len,mem
            --Bytestring# -> End
            | Return Var Var Value --off,len,(mem,ext,sto,tsto)
            --(Bytestring#,Ext,Sto,TSto) -> End
            --Stop deserves to be here as well
            | Stop Value --(mem,ext,sto,tsto)
  deriving (Eq,Ord,Read,Show,Data)
--invalid is strictly worse than revert 0 0 (modulo code size), so it should
--never be generated.

data ConstSet = ConstSet (Set Const)
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
--Dynamic value names, as distinct from functions and globals.
data Var = Mono {nameOfVar :: Name, typeOfVar :: T}
  deriving (Eq,Ord,Read,Show,Data)
data FunVar = FMono Name T --for auto-generated BBs
            | FPoly Name [T] T --for user-level functions
  deriving (Eq,Ord,Read,Show,Data)
data Value = Unit
           | Var Var
           | Pair Value Value
  deriving (Eq,Ord,Read,Show,Data)
newtype Pattern = P Value
  deriving (Eq,Ord,Read,Show,Data)
--If I made Pattern a data I could add Wild T, indicating an argument is
--unused...

--Integer literals, constructors, names for letrec-defined values.
newtype Const = MkConst E
  deriving (Eq,Ord,Read,Show,Data)

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

tupleV :: [Value] -> Value
tupleV = foldr Pair Unit

envT = tupleT [memory, calldata]
memory = TyCon "Memory#"
calldata = TyCon "Calldata#"
envV :: Value
envV = tupleV $ map Var [Mono "$mem" memory,
                         Mono "$cd" calldata]
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
pattern a :-># b = TyCon "->#" :$$ a :$$ b
--Cont a = (a,Env) -># End#
contT :: T -> T
contT a = tupleT [a,envT] :-># TyCon "End#"
--NB: a and b may not be closed over stk
fun2coreT :: T -> T -> T
fun2coreT a b = TyForall "stk" $
                let stk = TyVar "stk" in
                  contT $
                  foldr1 T.Pair [a, contT $ T.Pair b stk, stk]
