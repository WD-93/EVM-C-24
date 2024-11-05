{-# LANGUAGE LambdaCase #-}
module IR where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Except
import Data.Map(Map(..))
import qualified Data.Map as M
import Data.Set(Set(..))
import qualified Data.Set as S
import Control.Applicative ((<|>))

import DTs (Name(..), T(..))
--A SSA IR to represent straight-line segments

type IRVar = (Name,Int) --a counter for SSA
type Context name = [(name,IRT)]
--The type of IR exprs, which are either words or a static mem value used to
--track writes and prevent their reordering.
data IRT = Word T Int --the nth word of a C type
         | Mem --TODO add storage, tstorage etc
         | JumpDest [IRT]
  deriving (Eq,Ord,Read,Show)
data Op name = Op (Context name) --lhs
               Operator --op name
               [name] --arguments
  deriving (Eq,Ord,Read,Show)
--operator types; includes EVM opcodes less stack manipulation +
--C function calls
data Operator = Push StaticValue
              | Opcode String
              | Call --args: f, args, ret
  deriving (Eq,Ord,Read,Show)
data StaticValue = Const Integer
                 | LabelConst Int Name --do I need the int field?
  deriving (Eq,Ord,Read,Show)
--Anytime I make a call I can place the ret code somewhere else, but I can
--perform that splitting later.

--Straight-line code, a basic block; includes function calls.
data SLC name = SLC {
  slcStart :: Context name, --locals
  slcBody :: [Op name], --a bunch of "pure" lets
  slcTarget :: [name] --the remaining locals expected by the next structured SLC
  }
  deriving (Eq,Ord,Read,Show)

--while and if break up basic blocks; without knowing the words used by the
--next block I don't know what to set the target to.
--Are there any anonymous stack words that remain alive across BB boundaries?
--Yes, if f(do ..., 3) is allowed. Disallow it for now, get basic C working
--first.
--Then the target can just be a subset of the live locals (prune unused words).

--The treegraph algo takes an SLC in SSA form.

--If a name is out of scope, throw it
--Assume no repetitions in slcStart, that's to be checked earlier.
--Assume no repetitions in op lhs
--Doesn't check types, beyond distinguishing mem from words they're not really
--the IR's business.
ssa :: SLC Name -> Either Name (SLC IRVar)
ssa slc = evalState (runExceptT (ssaM slc)) M.empty
type SSA = ExceptT Name (State (Map Name Int))
ssaM :: SLC Name -> SSA (SLC IRVar)
ssaM slc = do
  start' <- mapM (\(nm,t) -> do
                     nm' <- newSSAName nm
                     return (nm',t)) $ slcStart slc
  body' <- mapM ssaOp $ slcBody slc
  target' <- mapM ssaName $ slcTarget slc
  return $ SLC start' body' target'
ssaName :: Name -> SSA IRVar
ssaName nm = do
  s <- get
  case M.lookup nm s of
    Just n -> return (nm,n)
    Nothing -> throwE nm
newSSAName :: Name -> SSA IRVar
newSSAName nm = do
  s <- get
  case M.lookup nm s of
    Just n -> do
      put $ M.insert nm (n+1) s
      return (nm,n+1)
    Nothing -> do
      put $ M.insert nm 0 s
      return (nm,0)
ssaOp :: Op Name -> SSA (Op IRVar)
ssaOp (Op lhs op args) = do
  args' <- mapM ssaName args
  lhs' <- mapM (\(nm,t) -> do
                   nm' <- newSSAName nm
                   return (nm',t)) lhs
  return $ Op lhs' op args'

--Invariant: the ops of a SSA'd SLC only use args which are in scope.
--Prior to CSE, after (x,n+1) has been assigned (x,n) will no longer be used
--and you can stop counting it.
--Now to count uses and turn into a treegraph.
--Ops may return multiple vars; op1 <- op2 iff any of the values in op2's lhs
--are in op1's args. Count the number of ops which use any of the the lhs vars.
--Each op is uniquely identified by its LHS; map from vars in the LHS to the
--LHS.
--while f() do
-- ...
--Since truthy involves an or over every word returned by f(), it could
--create a false appearance of multiple use. Add sum and or ops?
--I need to count each var use in order to consume individual vars...
--Whenever I emit an op, decrement the uses of its args
--An op may use the same var twice! But no need to count that in var uses.
--Count:
--op <- op dependencies; that's used for treegraph partition.
--op <- var uses (max 1 per op); that's used for consuming vs duping

--SSA ensures correct sequencing of memory writes and reads; between writes
--read order is flexible, reads are dependent on the last byte.
--Invariant before mem region splitting is supported: all writes are in
--sequential order.

--Treegraph property: each root is either in slcTarget or is multiply used;
--each internal node is singly used.
--Problem: since ops can return multiple words, they're not simple trees of
--exprs.
--First, just form a graph by following the target vars.

--for op@(lhs = f vars), for var in lhs, m[var] = op
type Originators = Map IRVar (Op IRVar)
originators :: [Op IRVar] -> --SSA ops
               Originators --creator of each non-pruned IRVar
originators ops = M.fromList $ do
  op <- ops
  let Op lhs _ _ = op
  let vars = map fst lhs
  var <- vars
  return (var,op)
--Given an slcTarget and originators, count var uses and op -> op uses
--A var being in target does not count as an op->op use.
{-
Algo: given var, look up op; if op's been explored halt
let (lhs = f vars) = op
for each unique op' on which op depends, increment op->op uses [op']
for each unique var on which op depends, increment var uses [var]
 and recurse on var
-}
--Edge case: ops which produce target vars may have 0 op-op uses; target vars
--may have 0 op-var uses.
--Add an op and var use for target so ops with 1 op-op use aren't wrongly
--treated as internal to a tree.
data CUState = CUS {cusExplored :: Set (Op IRVar),
                    cusVarUses :: Map IRVar Int,
                    cusOpUses :: Map (Op IRVar) Int
                   }
type CountUses = ReaderT Originators (State CUState)
countUses :: [IRVar] -> Map IRVar (Op IRVar) -> CUState
countUses tar orig =
  execState (runReaderT action orig) $
  CUS S.empty M.empty M.empty
  where action = do
          mapM countUsesM tar
          --Count the target as an op
          --TODO merge copy-paste code
          opset <- S.fromList <$> mapM getOrig tar
          let varset = S.fromList tar
          mapM_ incVarUses varset
          mapM_ incOpUses opset
countUsesM :: IRVar -> CountUses ()
countUsesM var = do
  op <- getOrig var
  expl <- gets cusExplored
  if S.member op expl
    then return ()
    else do
    let Op lhs f vars = op
    --For each unique op', increment op->op uses [op']
    opset <- S.fromList <$> mapM getOrig vars
    mapM_ incOpUses opset
    --For each unique var...
    let varset = S.fromList vars
    mapM_ incVarUses varset
    mapM_ countUsesM varset
getOrig :: IRVar -> CountUses (Op IRVar)
getOrig var = do
  orig <- ask
  --There should be no chance of failure here
  case M.lookup var orig of
    Just op -> return op
    _ -> error $ "Something went wrong in getOrig " ++ show var ++ "!"
incOpUses :: Op IRVar -> CountUses ()
incOpUses op = modify (\cus ->
                         cus{cusOpUses = incMap op $ cusOpUses cus})
incVarUses :: IRVar -> CountUses ()
incVarUses var = modify (\cus ->
                         cus{cusVarUses = incMap var $ cusVarUses cus})
incMap k = M.alter (\mn -> ((+1) <$> mn) <|> Just 1) k

--CUState gives me a set of relevant ops and the use count of each op;
--now I must divide the graph into a treegraph: a map from tree roots
--(ops) to the full trees.
data OpTree = OpNode (Op IRVar) [Either (Op IRVar) OpTree]
  --Source ops of the vars; either an external ref or subtree.
  --May be duplicated, which means you later need to track them to avoid
  --repeated subtree placement.
  --Trivial tree placement may be inefficient: consider
  --x1,x2,... <- op1, y <- op2, args = [x1,y,x2...]
  --There are no trees which are just a top-level external ref,
  --hence there's no OpTree constructor for it
  deriving (Eq,Ord,Read,Show)

--cusExplored gives us all relevant ops;
--originators gives us the deps of each op.
--cusOpUses tells us which ops have their output used by multiple ops.
--vars gives us the initial ops from which to start the algo (note the vars
--may be entirely independent expressions)
--Argh: target should be a proper op in order to have its own tree?
splitIntoTrees :: [IRVar] -> CUState -> Originators -> Map (Op IRVar) OpTree
splitIntoTrees vars cus origs = undefined
{-
Read: CUState, Originators
State: trees already constructed
Algo (op):
 
-}
