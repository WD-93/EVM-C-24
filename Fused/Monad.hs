{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Fused.Monad where

--The monads used for implementing the fused phase
--(monomorphization, structured compilation, sizeof computation, serialization,
--global layout).

import AST.DTs
import qualified AST.DTs as A
import Const.Const
import Structured.DTs
import qualified Structured.DTs as IR
import Core.RestrictedCore
import Core.PrimTypes
import Mono.Mono (instT,bindT,BindError(..))

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Except
import Control.Monad

--The main monad:
--Monomorphization, structured IR generation, datatype sizeof calculation,
--const serialization and global layout interleaved in one phase.
--Simple solution: a RWSE monad
--No need for a capability class, just lift when in FusedFunM?
newtype FusedM a = FM {runFusedM :: ReaderT Module
                     (StateT FusedS (Except FusedError)) a
                   }
  deriving (Functor, Applicative, Monad,
            MonadReader Module,
            MonadState FusedS,
            MonadError FusedError
           )
type MonoT = (Name,[T])
data FusedS = FS {
  --To prevent infinite loops in recursive funs
  fsVisitedFuns :: Set (Name,[T]),
  --Will be copied to Structured
  fsDefuns :: Map FunVar (BranchValue,[Stmt]),
  --To prevent infinite loops in code g = <e that depends on g>
  fsVisitedGlobals :: Set Name,
  --Code global g => label g(offset: 0, len: 2) : Ptr Code t
  --other g => off : Ptr r t
  --The code global's initializer is also included.
  --Q: Should I trim right-padding when placing datatypes in bytecode?
  fsGlobals :: Map Name (Either (T,Serialized) (Region,T,Integer)),
  --Datatypes:
  fsVisitedDatatypes :: Set MonoT,
  --We currently don't record internal padding
  fsSizeof :: Map MonoT Integer,
  --Monomorphized E recorded for symbolic opts
  fsTags :: Map (Name,[T]) (E,Serialized), --Con@ts => tag
  fsOffsets :: Map (Name,[T]) Integer, --field@ts => off for UBCons
  --A general-purpose counter; used for allocating IR var names to start with.
  fsCtr :: Integer
  }
  deriving (Eq,Ord,Read,Show)
initFusedS = FS {
  fsVisitedFuns = S.empty,
  fsDefuns = M.empty,
  fsVisitedGlobals = S.empty,
  fsGlobals = M.empty,
  fsVisitedDatatypes = S.empty,
  fsSizeof = M.empty,
  fsTags = M.empty,
  fsOffsets = M.empty,
  fsCtr = 0
  }
data FusedError = GenericFE String
                | NoMain
                | IlltypedMain BindError T
  deriving (Eq,Ord,Read,Show)

--Compiling f: S -> E <-> P
--In addition to the capabilities of FusedM, the FusedFunM monad must
--have additional state: the scope and inLoop. It must also emit Stmts.
data FusedFunR = FFR (Name,[T])
data FusedFunS = FFS {ffsScope :: [Var],
                      ffsInLoop :: Bool
                     }
  deriving (Eq,Ord,Read,Show)
newtype FusedFunM a = FFM {runFFM :: ReaderT FusedFunR
                            (WriterT [Stmt]
                             (StateT FusedFunS
                              FusedM)) a
                          }
  deriving (Functor, Applicative, Monad,
            MonadReader FusedFunR,
            MonadWriter [Stmt],
            MonadState FusedFunS,
            MonadError FusedError)
liftFused :: FusedM a -> FusedFunM a
liftFused m = FFM $ lift $ lift $ lift m

--Alloc off the general-purpose counter
alloc :: FusedM Integer
alloc = do
  fs <- get
  let n = fsCtr fs
  put fs{fsCtr = n + 1}
  return n

--TODO use capability classes
--The MonadError instance for FusedFunM should have its error wrapped in
--InFun (reader input f) when run in FusedM.

getScope :: FusedFunM [Var]
getScope = gets ffsScope
putScope :: [Var] -> FusedFunM ()
putScope scope = modify (\ffs->ffs{ffsScope=scope})

--Given a dest list and a source list of Word Vars, copies source to dest.
--If the lengths are unequal, that's a compiler error.
--No type checking is done; it can be used to coerce
copyTo :: [Var] -> [Var] -> FusedFunM ()
copyTo dst src
  | length dst /= length src = error "Compiler error in copyTo"
  | otherwise = zipWithM_ (\to from ->
                             emitPrim ([to],[]) "copy" ([from],[])) dst src
--I got tired of typing FusedFunM
type FFM = FusedFunM
--Copies the given word var to a new var with the given type.
copy :: T -> Var -> FFM Var
copy t v = do
  w <- newVar t
  copyTo [w] [v]
  return w
--Copy vars without modifying the type
copyVars :: [Var] -> FFM [Var]
copyVars xs = do
  let ys = mapM (\(Mono x t) -> newVar t) xs
  copyTo ys xs
  return ys

--Emits a primop with the given lhs and rhs
emitPrim :: Value -> Name -> Value -> FusedFunM ()
emitPrim lhs primop rhs = tell [lhs IR.:= (Op primop, rhs)]

--Emits an EVM op that consumes two words and pushes a Word, with no additional
--effects to track. Autogens the lhs.
op2 :: Name -> Var -> Var -> FusedFunM Var
op2 primop a b = do
  v <- newVar (W (UInt 32) 1)
  emitPrim ([v],[]) primop ([a,b],[])
  return v
--Ditto for 1 argument
op1 :: Name -> Var -> FusedFunM Var
op1 primop a = do
  v <- newVar (W (UInt 32) 1)
  emitPrim ([v],[]) primop ([a],[])
  return v
--Always returns a W (UInt 32) 1, i.e. a Word.
--Truncated to 32B.
--Precondition: n >= 0 (EVMC expresses negative numbers as negation of
--positive ones).
pushK :: Integer -> FusedFunM Var
pushK n = do
  let ser = serWord n
  w <- newVar (W (UInt 32) 1)
  tell [([w],[]) IR.:= (Push ser, ([],[]))]
  return w

--The scope information is embedded in the stmt by the caller
emitStmt :: Stmt -> FFM ()
emitStmt stmt = tell [stmt]

--Generates a new Var with the given Core type
newVar :: T -> FusedFunM Var
newVar t = do
  n <- liftFused alloc
  return $ Mono ("$anon"++show n) t
