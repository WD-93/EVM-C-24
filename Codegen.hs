{-# LANGUAGE LambdaCase #-}
module CodeGen where

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S

import DTs
import Asm

--Convert C code to a list of SLSes
--Each SLS has a continuation, which may be:
--none (stop, return, revert, invalid),
--static
--ifte th el (assumes the cond word is on the top of the stack)
--dynamic (jump to unknown)
--Only static return addresses are pushed; if a placed call to a function may
--return then its return continuation must be placed.

--IR: operate on words. Branches terminate a SLS.
--SSA? That would let you forget old versions of vars you've DUP'd, making
--the new var authoritative.
--Each SLS expects certain vars on the stack; a branch A -> B creates a
--coherency constraint: the stack layout of A must match what B expects.
--In particular, if a function has multiple call sites, all of them must
--follow the same calling convention.
--If a function may be dynamically called, you must place an instance with
--the default calling convention.
--No stack shuffling instructions in the IR, just a set of vars?

--For now, no IR; just compile directly from EVM C.
--First opt at the C level: inlining etc.
--Generate a single asm blob, starting from main :: () -> ().
--Each function has a set of statically mentioned functions; each of them must
--be placed.
--If a function has a single call site, inline it.
--If it has multiple, place it at the first call site.
--Future opt: place it at the most frequently executed call.
--A simple heuristic for execution frequency: every branch is 50/50.
--Future: inline small functions. Nested calls can use local gotos.

--I'll try to do type checking and codegen simultaneously.
--codegenDefun, codeGenS, codeGenE; all can call each other.
--Globally readable: the module
--Global state: set of already placed functions
--State per defun:
--a pool of anon labels
--locals: [(Name,T)]
--Output: Asm
--First, support only var = e and function args = (x,y,z)
--Style: CodeGen is CamelCase
--I wish types had ($)...
type CodeGen = ExceptT CodeGenError (
  ReaderT Module (
      WriterT [Asm] (
          State CodeGenState
          )))
data CodeGenError = NoSuchFunction Name
                  | DefunWithNonFunctionType Name T
  deriving (Eq,Ord,Read,Show)
data CodeGenState = CGS {placedFunctions :: Set Name,
                         anonLabelCtr :: Int,
                         localScope :: [(Name,T)]
                        }
  deriving (Eq,Ord,Read,Show)
runCodeGen :: CodeGen a -> Module -> CodeGenState ->
  (Either CodeGenError a, [Asm], CodeGenState)
runCodeGen cg m s =
  case flip runState s $ runWriterT $ flip runReaderT m $ runExceptT cg of
    ((ei,asm),s') -> (ei,asm,s')

--Why CodeGen and not just an Int? Because I'll extend the lang with
--user-defined types later.
sizeof :: T -> CodeGen Int
sizeof = \case
  Int _ n -> return n
  _ :-> _ -> return 2
  Struct fields -> sum <$> mapM fieldSize fields
fieldSize :: (Padding,Name,T) -> CodeGen Int
fieldSize (padding,_,t) = do
  n <- sizeof t
  return $ padModulo (case padding of
                        BitPad -> 1
                        BytePad -> 8
                        WordPad -> 256) n
wordSizeof :: T -> CodeGen Int
wordSizeof t = do
  n <- sizeof t
  return $ padModulo 256 n `div` 256

--Takes a desugared module, places from the specified "external" functions.
--Unused internal functions are omitted. If main is present, places it first.
codeGenModule :: Set Name -> Module -> CodeGen ()
codeGenModule fset mod = do
  let fs = S.toList fset
  if S.member "main" fset
    then codeGenFunction "main"
    else return ()
  mapM_ codeGenFunction fs
codeGenFunction :: Name -> CodeGen ()
codeGenFunction f = do
  placed <- hasBeenPlaced f
  --Check whether f has been placed already; if not, place it
  if placed
    then return ()
    else do
    Defun _ t args body <- getDefun f
    case t of
      a :-> b -> undefined
      _ -> throwE $ DefunWithNonFunctionType f t
--Acceptable LHS for a function (for now): _, x, tuples.
--Those divide the argument expr into locals, each in separate words.
--In future, allow binding locals to struct fields. Implement that by
--extracting the values.
--Invariant: Each local corresponds to unique words on the stack which do not
--overlap with other locals.
--In assignment and case, the old expr is discarded and the newly bound vars
--do not point into it.

--This is run after the relevant e is on the stack; function calls start with
--anon:a on the stack. Hack: the empty string signals anonymous values.
--If the top of the stack is a local, something's gone wrong.
--Assignment to _ 
consumeAndBind :: Pat -> CodeGen ()
consumeAndBind = undefined
    
--Checks if a function has been placed already
hasBeenPlaced :: Name -> CodeGen Bool
hasBeenPlaced f = S.member f <$> placedFunctions <$> get

--Errors if the name is not a function
getDefun :: Name -> CodeGen D
getDefun f = do
  md <- M.lookup f <$> defuns <$> ask
  case md of
    Nothing -> throwE $ NoSuchFunction f
