{-# LANGUAGE LambdaCase #-}
module Codegen where

import Core.RestrictedCore
import Core.SSA
import Const.Const (Serialized(..))
import Opt.AI
import Opt.HTraversable (Id(..))
import Asm

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad

--At long last, the Core optimizer is good enough that it's worth generating
--code from it. That allows compiler debugging using test programs with output
--too large to read.
--Codegen is broadly similar to the code generator for the monomorphic EVMC
--(Stack.hs), with some key differences.
--I) Rather than every CFG IR function being EVMC calling convention-compliant,
--the CALL entrypoint and default exit are explicit Core functions: $trueMain
--and $stop. That enables them to be optimized alongside user basic blocks
--(BBs), whereas in monomorphic EVMC a mandatory Asm prologue is used instead.
--That was necessary because CALLs begin with an empty stack, which is not
--compatible with the EVMC calling convention where the return address $ret
--must be on the stack.
--II) In monomorphic EVMC, control flow was static: edges between BBs were
--represented as Ints, and calls were represented as straight-line ops.
--That simplified intraprocedural inlining and eta reduction, but prevented
--interprocedural inlining. The latter is essential for polymorphic EVMC, since
--primfuns are represented as ordinary functions in the Structured IR
--(albeit with a compiler-generated definition) and the functional style used
--in the standard library depends on cheap calls (c.f. Stdlib/Arith.evmc's
--returnValue).
--In polymorphic EVMC, jump/i destinations are instead represented using Vars,
--the same representation as any other dynamic values on the stack.
--III) To enable calls and intraprocedural jumps to be represented with the
--same Jump construct, it's necessary to fix the expected stack layout in
--advance. Where monomorphic EVMC lazily sets the stack ordering per BB g to
--whatever the resulting layout of the first BB f to jump to g, polymorphic
--EVMC's Structured IR specifies stack layout at each branching construct.
--That information is then used to set Core function lhses.
--While that complicated optimization (necessitating a branch param pruning
--rule), the end result is that the BB code generator can always make use of
--the target stack layout to generate more efficient stack code.

--Fallthrough: of BB g's non-continues preds, static jumps and else branches
--are candidates. Of those, only one can be selected to fall through.
--Remaining non-continues preds are forced jumps; iff a BB has >0 forced jump
--preds then it needs a jumpdest.
--If f falls through to g:
--if its branch is jump (dest:rest,ss), omit dest from the stack target and
--prune the push g op.
--if jumpi elf (dest:cond:rest,ss), omit [push2 elf, jump] after the jumpi.
--In either case, f must be placed directly before g.
--Prior to execution intensity analysis, I'll use a crude measure of intensity
--to decide which candidate to choose: branch distance from $trueMain.
--I'll prefer fallthrough from jumps vs jumpis, on the assumption that the
--jump is more likely to be taken if it's at the same depth.

--codegen algo overview:
--Functions:
--Compute distance from $trueMain per BB.
--Determine fallthrough and jumpdest requirement per BB
--Compile each BB to [Asm]
--Place: $trueMain first, then in arbitrary order subject to fallthrough
--constraint.
--JTs: Place JTs in arbitrary order.
--End of .text: place code global initializers in arbitrary order, except
--codeOffset must be last if present (it points to constructor arguments).
--TODO: compress by exploiting shared suffixes/prefixes.
--The same could be done for BBs and JTs...

--What can go wrong?
--1) A dup or swap out of range in a BB due to too large stack.
--2) The contract exceeding the 24kB size limit.
--AsmError and undefined labels are compiler errors.
data CodegenError = InFunction (FunVar,CodegenFunError)
                  | ContractSizeLimitExceeded Int
  deriving (Eq,Ord,Read,Show)
data CodegenFunError = DupOutOfRange Var Int
                     | SwapOutOfRange Var Int
  deriving (Eq,Ord,Read,Show)
--The result of compiling a contract; TODO add interface info in order to
--support ergonomic calls using datatypes defined in the contract.
--That will require modifying the pipeline to save DT info.
--Exposing global pointers and functions would also be possible, but would
--mess with optimizations; you'd need to mark globals and monomorphic functions
--as exported.
data CompiledContract = CompiledContract {
  ccText :: [Int]
  }
  deriving (Eq,Ord,Read,Show)

codegen :: OptCore -> Either CodegenError CompiledContract
codegen core =
  case codegenFuns $ coreDefuns core of
    Left fcge -> Left $ InFunction fcge
    Right fasm ->
      let jtasm = codegenJTs $ coreJTs core
          gasm = codegenStatic $ coreStatic core
          asm = fasm ++ jtasm ++ gasm
      in case assemble asm of
           Left asmError -> error $ "Compiler error (asmError):" ++
                            show asmError
           Right obj ->
             let (undefinedLabels,bytes) = toExe obj
             in if not $ S.null undefinedLabels
                then error $ "Compiler error (undefined labels): " ++
                     show undefinedLabels
                else let len = length bytes
                     in if len > 24000
                        then Left $ ContractSizeLimitExceeded len
                        else Right $ CompiledContract {ccText = bytes}
--Place JTs in arbitrary order.
codegenJTs :: Map FunVar (a,[FunVar]) -> [Asm]
codegenJTs = placeArbitrary (codegenJT . snd)
codegenJT :: [FunVar] -> [Asm]
codegenJT = (>>= (\f -> [
                    Opcode "jumpdest",
                    PushLabel 2 $ LNamed f,
                    Opcode "jump"
                    ]))
--Place code global initializers in arbitrary order.
codegenStatic :: Map FunVar Serialized -> [Asm]
codegenStatic = placeArbitrary codegenCG
--What do if serLength and serSizeof conflict? I'll just pack initializers
--densely for now, meaning that values with length < sizeof (e.g. Nil)
--may contain nonzero bytes in their right-padding.
codegenCG :: Serialized -> [Asm]
codegenCG = map (\case
                    Left bs -> Bytes bs
                    Right (off,len,lab)
                      | off /= 0 ->
                        error $ "Compiler error: can't handle nonzero label "
                        ++ "offset!"
                      | let -> UseLabel len $ LNamed lab
                ) . serContent

placeArbitrary :: (a -> [Asm]) -> Map FunVar a -> [Asm]
placeArbitrary a2asm =
  concat . M.mapWithKey (\f a -> PlaceLabel (LNamed f) : a2asm a)

--Binding the important string $trueMain to a name to detect typo bugs.
trueMain = "$trueMain"
--Given a Core program and its AI results, compute the distance from $trueMain
--per BB.
--Precondition: $trueMain is present, unreachable BBs have been pruned.
{-
Algo:
depth = {}
go 0 entrypoint
where
go d f =
 if f in depth:
  return
 else:
  depth[f] = d
  for each non-continue g in succs[f]:
   go (d+1) g
-}
computeDistance :: FrozenModState -> OptCore -> Map FunVar Int
computeDistance ms core =
  execState (go 0 trueMain) M.empty
  where
    go :: Int -> FunVar -> State (Map FunVar Int) ()
    go d f = do
      s <- get
      if M.member f s
        then return ()
        else do
        modify $ M.insert f d
        forM_ (nonContinues f) $ go $ d+1
    nonContinues f =
      case M.lookup f $ funInfo ms of
        Nothing -> error "!?"
        Just fi ->
          S.toList $ M.keysSet $ M.filter (== Normal) $ unId $ succs fi

--Note: the Core iset contains non-EVM ops emptyMem etc.
codegenFuns :: Map FunVar (BranchValue,OptFunRHS) ->
               Either (FunVar,CodegenFunError) [Asm]
codegenFuns = error "todo"
