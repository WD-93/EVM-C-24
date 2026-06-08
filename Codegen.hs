{-# LANGUAGE LambdaCase #-}
module Codegen where

import Core.RestrictedCore
import Core.SSA
import Const.Const (Serialized(..))
import Opt.AI
import Opt.HTraversable (Id(..))
import Opt.AbVar
import Opt.Opt (Fundef())
import Asm
import Util ((?))

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad
import Data.List (sort)

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

--TODO split out the part after asm in order to be able to debug (readable) asm
--rather than bytecode.
codegen :: OptCore -> Either CodegenError CompiledContract
codegen core =
  case codegenFuns core of
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
codegenFuns :: OptCore ->
               Either (FunVar,CodegenFunError) [Asm]
codegenFuns core = do
  --I could return this in Opt instead of recomputing it
  let Right ms = ai core
      f2dist = computeDistance ms core
  --For each BB, determine
  --1) If it will be jumped to by any BB or JT
  --2) Which (if any) f it will fall through to and vice versa.
  let (f2decdef,f2g,g2f) = decorateBBs f2dist ms core
  --Given that information, compile each BB to [Asm].
  f2asm <- sequence $ M.mapWithKey codegenBB f2decdef
  --Concatenate together chains of BBs that fall through to each other,
  --starting with the first.
  let head2asm = concatFallthroughChains f2g g2f f2asm
      --Place $trueMain's chain first, then the rest in arbitrary order.
      Just mainAsm = M.lookup trueMain head2asm
      rest = concat $ M.delete trueMain head2asm
  return $ mainAsm ++ rest

--For each f, get its non-continues preds.
--Split out those that are fallthroughable; if there are any, select the
--one with the lowest distance (from $trueMain) as the ft.
--Return the rest to the set; if it's nonempty then the f will be jumped to.
--FW: a JT could fall through to its last element, but that would require
--mixing fs and JTs. A function will never fall through to a JT (since if
--the index is constant you might as well jump to the f), but you could reduce
--code size by sharing an overlapping "push2 f, jump" at the cost of executing
--an unnecessary jumpdest.
{-
Algo:
f2ft = for each f, get the g it could fall through to
g2fset = invert that map
g2f = map select_best g2fset
f2g = reverse g2f
f2preds = non-continues predecessors
f will be jumped to if:
 #f2preds[f] > 1, or
 not (f in g2f) && #f2preds[f] > 0
f will fallthrough if: f in f2g
-}
decorateBBs :: Map FunVar Int -> FrozenModState -> OptCore ->
               (Map FunVar (Bool, --Will be jumped to
                            Bool, --Will fallthrough to jump dest or jumpi else
                            Fundef
                           ),
                Map FunVar FunVar, --f=>the g it falls through to
                Map FunVar FunVar  --g=>the f that falls through to it
               )
decorateBBs f2dist ms core =
  let f2fi_def = M.intersectionWith (,) (funInfo ms) $ coreDefuns core
      --f can fall through if:
      --1) It makes a static jump to a function.
      --2) It jumpis.
      f2ft = M.mapMaybe
             (\(fi,(_lhs,(_opMap,branch))) ->
                case branch of
                  Jump _mode (dest:_,_,_) ->
                    let Just destabv = fmap (unId.avVal) $ M.lookup dest $
                                      fiVars $ fiBodyInfo fi
                    in case unlabel destabv of
                         Just (Fun,f) -> Just f
                         _ -> Nothing
                  Jumpi elf _ -> Just elf
                  _ -> Nothing
             ) f2fi_def
      --for f=>g, out[g] insert= f
      --TODO optimize
      g2fset = foldr (\(f,g) ->
                        M.alter (Just . maybe (S.singleton g) (S.insert g)) g)
                        M.empty $
               M.toList f2ft
      --Select the best fallthrough
      --Note fs is nonempty for every key g
      g2f = M.map (\fs ->
                     --Associate fs with dist and branch
                     let f2dist_branch =
                           flip M.restrictKeys fs $
                           M.intersectionWith (,) f2dist $
                           M.map (\(_lhs,(_ops,branch)) -> branch) $
                           coreDefuns core
                         --Sort by them; fortunately Jump{} < Jumpi{}
                     in snd $ head $ sort $ map swap $
                        M.toList f2dist_branch
                  )
            g2fset
      f2g = M.fromList $ map swap $ M.toList g2f
  in (M.mapWithKey
      (\f (fi,def) ->
         --Number of non-continues (direct) predecessors
         let npreds = M.size $ M.filter (==Normal) $ unId $ preds fi
             --Whether f is jumped to:
         in (npreds > 1 || (not (M.member f g2f) && npreds > 0),
             --Whether f falls through:
             M.member f f2g,
             def
            )
      ) f2fi_def,
      f2g,
      g2f
     )
  where
    swap (a,b) = (b,a)
{-
--Unreachable JTs are pruned, so all the fs in JTs may be jumped to.
  let jtFs = S.fromList $ concat $ M.map snd $ coreJTs core
-}

--BBs with neither predecessor nor successor form 1-elem chains.
--The chain heads are those BBs not in g2f.
concatFallthroughChains :: Ord k =>
  Map k k -> --fallthrough
  Map k k -> --inverse fallthrough
  Map k [a] -> --compiled BBs
  Map k [a] --chain start => all BBs in chain
concatFallthroughChains f2g g2f f2asm =
  let heads = S.difference (M.keysSet f2asm) (M.keysSet g2f)
  in M.fromSet follow heads
  --I could optimize follow by fusing f2g and f2asm
  where follow f =
          let Just asm = M.lookup f f2asm
          in asm ++
             case M.lookup f f2g of
               Nothing -> []
               Just g -> follow g

--The trickiest part of codegen, hence why it's placed last.
--TODO exploit that only the top words of the stack (and not its height)
--matters if mstk is dead.
codegenBB :: FunVar -> --f
             (Bool, --May be jumped to
              Bool, --Falls through
              Fundef) ->
             Either (FunVar,CodegenFunError) [Asm]
codegenBB f (j,ft,(flhs,(opMap,branch))) = do
  --body depends on starting stack,
  --ops and their ordering constraints,
  --and the target stack.
  body <- codegenOps ft flhs opMap branch ? (,) f
  return $
    [PlaceLabel $ LNamed f] ++
    [Opcode "jumpdest" | j] ++
    body ++
    codegenBranch ft branch
--ft can only be true for Jump and Jumpi
--The ops have already placed the vars in the right position.
--It might appear that fallthrough saves two ops for jumpi and only one for
--jump, but that's not true since dest is removed from the target in jump
--fallthhrough.
codegenBranch :: Bool -> Branch -> [Asm]
codegenBranch ft = \case
  Jump {} -> [Opcode "jump" | not ft]
  Jumpi else_f _ ->
    [Opcode "jumpi"] ++
    if ft
    then []
    else [PushLabel 2 $ LNamed else_f,
          Opcode "jump"
         ]
  Revert {} -> [Opcode "revert"]
  Return {} -> [Opcode "return"]
  Stop {} -> [Opcode "stop"]
--Also returns the state vars for pruning (fallthrough may deaden the dest push
--op)
targetStack :: Bool -> Branch -> Value
targetStack ft = \case
  Jump _mode (ws,_,ss) -> (ws,ss)
  Jumpi _elf (ws,_,ss) -> (ws,ss)
  Revert v -> v
  Return v -> v
  --You could save a lot of gas here by relaxing the stack target when $stk
  --is dead, since [] ++ _ matches any stack.
  Stop v -> v

--Since dest may be pruned, opMap must be pruned as well. The remaining ops
--must be run.
--Convert state var borrow and consume into ordering constraints:
--If op2 borrows s produced by op1, op1 -> op2
--If opW consumes s borrowed by opR, opR -> opW
--For now, there is only one state var at a time per state type, so key by
--type.
--Prune redundant constraints: A->B->C dominates A->C, stack dependency
--dominates state dependency.
--Algo: for each A with direct edges to Bs, keep only the orthogonal Bs with
--greatest height. If B->C, then height(B) > height(C). Fun lhs vars have
--height 0.

--FW: exploit that vars in the source stack may have known values;
--if a constant is already on the stack, dup it instead of pushing the same
--constant.
--FW: replicate idempotent subexprs if it saves enough stack shuffling overhead.
--FW: if ToS is x,y,0 and garbage, use mcopy instead of pop.
--Full treegraph may not be optimal, but at least...
--Collapse the leftmost constant part of subtrees into atomic ops for
--planning purposes: op ~ (args,pushed,asm).
--Represent the asm using a DT with abstract Dup Var so its value is
--independent of when it's placed (which is unknown). Should the same be done
--for swap?
--If op pushes a var that is not used (possible for CALL, CREATE), fuse the
--POP and change effect to (args,Nothing,asm++POP).
--Is there any reason to use a list rather than Maybe for pushed?
--Vars in the target are never last-use, so they may be treated like
--constants: any use becomes a dup.
--Is that optimal? Consider target = x*5, where x,5 are on the stack and 5
--is garbage. You can mul instead of push1 5, mul, swap1, pop.
--Don't use constant info for now.
--FW: commutative reduction can be represented with a set rather than list.
--Partial state: v=reduce(op,vs) on the stack.
--Discover DAGs of commassoc ops with no external uses of intermediate
--reduces, convert to a single reduce.
--If two vars from a reduce (guaranteed to have no external uses!) are ToS,
--immediately apply op.

--Problem: ops : args => pushed, source, target, non-stack op dependencies.
--Big-step: generate a scheduling with as few dups, swaps, and pops as poss.
--Small-step: generate a sequence of dups, swaps and pops followed by the next
--op (or none if done).
--Is it always worth it to pop dead vars ToS? Consider
--g,y,...,x where you want to run op(x,y). If you swap you're left with
--garbage to deal with later...
--Non-commutative ops have stack constraint vs,rest where rest must contain
--the vars that will be used later.
--Their constraint is similar to 

--A suffix of the stack matches the target; it should never be touched again.
--If a var x will be last-used, it may be efficient to pause exec of the tree
--that last-uses x, eval the var y that replaces x at the same position,
--use it to "fish" out x with swap, then continue.
--If trees share constants and don't interfere, it may be worth doing the
--pushing of one to expose dupable constants for the other (stack space
--allowing). Avoid the tree abstraction entirely?
--If T2 after T1 and T2 uses v, then it definitely won't be last-used in T1.
codegenOps :: Bool -> BranchValue -> OpMap -> Branch ->
  Either CodegenFunError [Asm]
codegenOps ft flhs opMap branch = do
  --The target stack layout; depends on whether the branch falls through
  let (target,ss) = targetStack ft branch
      --The dest push op may be dead; prune all dead ops for simplicity
      --TODO opt: refcount vars so you can delete push without traversing ops
      ops = execState (mapM_ go $ target ++ ss) M.empty
  error "todo"
  where
    go :: Var -> State OpMap ()
    go v = do
      visited <- get
      if M.member v visited
        then return ()
        else case M.lookup v opMap of
               Nothing -> return () --It's a function lhs var
               Just op@(_lhs,(_primop,(ws,ss))) -> do
                 modify $ M.insert v op
                 mapM_ go $ ws ++ ss

--Stack scheduling is a tricky problem; it seems likely there's no polytime
--optimal algo, so it would be worth evaluating a range of heuristic
--strategies.
--The logic for extraction and simplification of the problem can be shared
--between them, so I'll write that first.

--State vars can be eliminated by computing the dependencies between ops:
--Computing consumer : Map Var op, producer : Map Var op,
--borrowers : Map Var (Set op), statevars : Set Var:
-- For each o:
--  for s in state args of o:
--   add s to statevars
--   if state lhs of o contains a var s' of the same type:
--    o consumes s
--    o produces s'
--   else:
--    o borrows s
--For now, ops are identified by Value; using an Int index might be worth
--investigating in future.
data StateVarUseInfo = SVUI {
  svuiConsumer  :: Map Var Value,
  svuiProducer  :: Map Var Value,
  svuiBorrowers :: Map Var (Set Value)
                           }
  deriving (Eq,Ord,Read,Show)
--I have to normalize the opmap yet again... TODO change its repr.
normalizeOpMap :: OpMap -> Map Value (PrimOp,Value)
normalizeOpMap = M.fromList . M.elems
stateVarUseInfo :: OpMap -> StateVarUseInfo
stateVarUseInfo ops =
  execState (mapM_ go $ M.toList $ normalizeOpMap ops) $
  SVUI M.empty M.empty M.empty
  where
    go :: (Value,(PrimOp,Value)) -> State StateVarUseInfo ()
    go (lhs@(_,slhs),(_,(_,srhs))) =
      --Map state type to output var to efficiently identify consumes
      --Invariant: there is at most one var per state type.
      let t2sv = M.fromList [(typeOfVar v, v) | v <- slhs]
      in forM_ srhs
         (\s ->
            case M.lookup (typeOfVar s) t2sv of
              Nothing -> lhs `borrows` s
              Just s' -> do
                lhs `consumes` s
                lhs `produces` s'
         )
    --TODO use lenses to elim boilerplate
    borrows :: Value -> Var -> State StateVarUseInfo ()
    lhs `borrows` s =
      modify $
      \svui->svui{
        svuiBorrowers =
            M.alter (Just . maybe (S.singleton lhs) (S.insert lhs)) s $
            svuiBorrowers svui
        }
    consumes :: Value -> Var -> State StateVarUseInfo ()
    lhs `consumes` s = modify $
      \svui->svui{
        svuiConsumer =
            M.insert s lhs $
            svuiConsumer svui
        }
    produces :: Value -> Var -> State StateVarUseInfo ()
    lhs `produces` s = modify $
      \svui->svui{
        svuiProducer =
            M.insert s lhs $
            svuiProducer svui
        }
--Uses of s must be after its producer (if any); borrows of s must be before
--its consumer (if any).
--Computing direct deps : Map op (Set op):
--deps = {}
--For each s in statevars:
-- if has producer p:
--  for each o in borrowers[s]: deps[o] += p
--  deps[consumer[s]] += p
-- if has consumer c:
--  deps[c] U= borrowers[s]
--Redundant state deps can be pruned:
--We have deps : op => Set op
--Compute preds : Map op (Set op)
--Pruned deps:
--For o@(lhs = op rhs):
-- os = ops(rhs)
-- os' = os U map preds os
-- deps[o] = deps[o] difference os'

--Commassoc reduces: replace trees of commassoc ops with a single
--reduce op vs.
--Commassoc: add, mul, smul, and, or, xor.
--Refinement: and, or are idempotent, so duplicate vars can be pruned.
--Duplicate vars in xor cancel.
--This needs to be updated in tandem with Opt, which may make some
--transformations dead.
--Absorbents (x*0=0) already handled by AI.
--Identities (x*1=x) yet to be handled.
--x xor ~0 = ~x

--Last-use analysis:
--If v in target, it'll never be last-used.
--The last-use candidate ops are those o which use v and have no successor o'
--which uses v. If there is only one candidate op, v is definitely last-used
--in it. Note the op may use v in several places.
--Heuristics:
--Q: should ops with no last-uses be treated as ~pushes? Then trees can be
--combined recursively.
--Fuse op with unused word with pop.
--If an op's last-uses are ToS, push its other args and swap into correct pos;
--adjust the push order so that x is pushed, then swapped into pos(last)
--when last should be ToS.
--An op with pushed () and no last-uses should be run as soon as it's
--runnable.
