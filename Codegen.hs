{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving, FlexibleInstances #-}
module Codegen where

import Core.RestrictedCore
import Core.SSA hiding (debugFlag,unsafePrint)
import Const.Const (Serialized(..))
import Opt.AI hiding (debugFlag,unsafePrint)
import Opt.HTraversable (Id(..))
import Opt.AbVar
import Opt.Opt (Fundef())
import Asm
import Util ((?), unsafePrint')

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad
import Data.List (sort)
--For more efficient ProblemSpec:
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IM
--For treegraph:
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IS
--For Stack monad:
import Control.Monad.Except
import Control.Monad.Writer
import Data.List (elemIndex,nub)

debugFlag = True
unsafePrint str = unsafePrint' debugFlag str

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
data CodegenFunError = DupOutOfRange String Int
                     | SwapOutOfRange String Int
                     --DupOutOfRange and SwapOutOfRange can be triggered by
                     --having too many live stack vars, which codegen can't
                     --do anything about since it's not allowed to spill;
                     --that's a user error, not a compiler error.
                     --StackError is thrown if there is a compiler error in
                     --the stack scheduler, but I return it as a value rather
                     --than throw a Haskell exception for debugging purposes.
                     | StackError StackError
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
codegen core = do
  asm <- codegen' core
  case assemble asm of
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
--Useful for reading asm output
codegen' :: OptCore -> Either CodegenError [Asm]
codegen' core =
  case codegenFuns core of
    Left fcge -> Left $ InFunction fcge
    Right fasm ->
      let jtasm = codegenJTs $ coreJTs core
          gasm = codegenStatic $ coreStatic core
          asm = fasm ++ jtasm ++ gasm
      in return asm
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
  --unsafePrint $ "BB keys: " ++ show (M.keys f2asm)
  --unsafePrint $ "f2g: " ++ show f2g
  --unsafePrint $ "g2f: " ++ show g2f
  let head2asm = concatFallthroughChains f2g g2f f2asm
      --Place $trueMain's chain first, then the rest in arbitrary order.
      Just mainAsm = M.lookup trueMain head2asm
      rest = concat $ M.delete trueMain head2asm
  --unsafePrint $ "Heads: " ++ show (M.keys head2asm)
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
                        M.alter (Just . maybe (S.singleton f) (S.insert f)) g)
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
      problemSpec = mkProblemSpec flhs ops target
  solveProblemSpec problemSpec
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

mkProblemSpec :: BranchValue -> OpMap -> [Var] -> ProblemSpec
mkProblemSpec (src,_mstk,_ss) ops target =
  let op2def = normalizeOpMap ops
      deps = stateDepGraph $ stateVarUseInfo op2def
      v2op = M.map fst ops
      direct_stack = directStackPreds v2op op2def
      --Note: pruned_deps may contain no entry for an op, equivalent to S.empty
      pruned_deps = pruneDeps direct_stack deps
      --Need to convert the op Map to an IntMap; the dep sets must be
      --converted to refer to the new keys.
      --Note the map is invertible and monotonic; TODO use that to optimize.
      op2int = M.fromList $ zip (M.keys op2def) [0..]
      op2intdeps = M.map (S.map (\op ->
                                    let Just n = M.lookup op op2int
                                    in n
                                )
                         ) deps
      op2spec = M.mapWithKey (\op@(lhsws,_) (primop,(rhsws,_ss)) ->
                                OS {
                                 osArgs = map nameOfVar rhsws,
                                 osRet = case lhsws of
                                           [] -> Nothing
                                           [w] -> Just $ nameOfVar w
                                           _ -> error "!?",
                                 osOp = primop,
                                 osStateDeps = case M.lookup op op2intdeps of
                                                 Nothing -> S.empty
                                                 Just intdeps -> intdeps
                                 }) op2def
  in PS {
    psSource = map nameOfVar src,
    --The IntMap is dense
    psOps = IM.fromList $ zip [0..] $ M.elems op2spec,
    --For each op which returns a v, v => its IntMap index
    psVar2Op =
        let v2op =
              M.mapKeys nameOfVar $
              M.mapMaybe (\(op@(ws,_ss),_rhs) ->
                             case ws of
                               [] -> Nothing
                               [w] -> Just op
                               _ -> error "!?"
                         ) ops
        in M.compose op2int v2op,
    psTarget = map nameOfVar target
    }

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
stateVarUseInfo :: Map Value (PrimOp,Value) -> StateVarUseInfo
stateVarUseInfo ops =
  execState (mapM_ go $ M.toList ops) $
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
--For each s,bs in borrowers:
-- if p = producer[s]:
--  for each o in bs:
--   deps[o] += p
-- if c = consumer[s]:
--   deps[c] U= bs
--For each s,c in consumers:
--  deps[c] += producer[s]
stateDepGraph :: StateVarUseInfo -> Map Value (Set Value)
stateDepGraph SVUI {
  svuiConsumer = consumer,
  svuiProducer = producer,
  svuiBorrowers = borrowers
  } =
  flip execState M.empty $ do
  forM_ (M.toList borrowers)
    (\(s,bs) -> do
        case M.lookup s producer of
          Just p ->
            forM_ (S.toList bs)
            (\o -> insertDep o p)
          _ -> return ()
        case M.lookup s consumer of
          Just c -> insertDeps c bs
          _ -> return ()
    )
  forM_ (M.toList consumer)
    (\(s,c) ->
       case M.lookup s producer of
         Just p -> insertDep c p
         _ -> return ()
    )
    where
      insertDep :: Value -> Value -> State (Map Value (Set Value)) ()
      insertDep post pre =
        modify $ M.alter (Just . maybe (S.singleton pre) (S.insert pre)) post
      insertDeps :: Value -> Set Value -> State (Map Value (Set Value)) ()
      insertDeps post pres =
        modify $ M.alter (Just . maybe pres (S.union pres)) post
--Redundant state deps can be pruned:
--We have deps : op => Set op
--Compute direct stack preds : op => Set op
--Precondition: the ops form a DAG.
directStackPreds ::
  Map Var Value ->            --var => parent op
  Map Value (PrimOp,Value) -> --normalized op map
  Map Value (Set Value)       --op => ops it has a stack dep on
directStackPreds v2op =
  M.map $ \(_,(ws,_ss)) ->
            S.fromList $ do
  v <- ws
  case M.lookup v v2op of
    --The var must be from lhs
    Nothing -> []
    Just op -> [op]

--output[k] includes k' iff there is a path from k to k' in input
--(viewed as a graph where k1 -> k2 iff input[k1] includes k2).
--Precondition: the graph is acyclic and has no edges to keys not in the
--graph.
transitiveClosure :: Map Value (Set Value) -> Map Value (Set Value)
transitiveClosure input =
  execState (mapM_ go $ M.keys input) M.empty
  where
    go :: Value -> State (Map Value (Set Value)) (Set Value)
    go k = do
      mkset <- gets (M.lookup k)
      case mkset of
        Just kset -> return kset
        _ ->
          case M.lookup k input of
            Just dist1 -> do
              dist2plus <- S.unions <$> mapM go (S.toList dist1)
              let indirect = S.union dist1 dist2plus
              modify $ M.insert k indirect
              return indirect
--Pruned deps:
--Need direct stack preds and indirect full (stack+state) preds.
--For each op o, retain only those direct state deps that are not in
--direct stack preds[o] or indirect full preds of o's direct full preds.
--Note: no key in direct_state means S.empty.
--Note state dep is more inclusive than simply user->producer edges, as
--it also includes consumer->borrower.
pruneDeps ::
  Map Value (Set Value) -> --direct stack deps
  Map Value (Set Value) -> --direct state deps
  Map Value (Set Value)    --non-redundant direct state deps
pruneDeps direct_stack direct_state =
  let direct_full = M.unionWith S.union direct_state direct_stack
      indirect_full = transitiveClosure direct_full
  in M.mapWithKey (\op state ->
                     let Just stack = M.lookup op direct_stack
                         Just full = M.lookup op direct_full
                         indirect = S.unions $ map
                           (\op -> case M.lookup op indirect_full of
                                     Just ops -> ops
                                     _ -> error "!?")
                           $ S.toList full
                     in S.difference state (S.union stack indirect))
     direct_state

--The DT representing stack scheduling problems, to be consumed by stack
--schedulers:
--No handling of commassoc reduces for now; I'll figure out how to do so in
--the solver, then port it back.
--The (stack) Vars are converted to Strings because typeOfVar is not
--required; better to sanitize early and in one place than across all users.
data ProblemSpec = PS {
  --source stack (invariant: no duplicates)
  psSource :: [String],
  --op intmap: Int => (argws,retws,asm), state dep graph
  psOps :: IntMap OpSpec,
  --A redundant map map var => Int
  psVar2Op :: Map String Int,
  --target stack (duplicates allowed)
  psTarget :: [String]
  }
  deriving (Eq,Ord,Read,Show)
data OpSpec = OS {
  osArgs :: [String],
  osRet :: Maybe String, --always 0 or 1 words
  --I could use a list of stack instrs here to allow merging, but that would
  --make osArgs (the vars that must be ToS when the op is run) deceptive, as
  --merging an op with dup of its args would obscure that it depends on them.
  osOp :: PrimOp,
  osStateDeps :: Set Int
  }
  deriving (Eq,Ord,Read,Show)

--The type of solvers. Needs to throw a CodegenFunError because the BB may be
--unrealizable due to too many vars on stack causing dup or swap out of range.
--Spilling is currently not possible because I have no scratch of unbounded
--size and alloc is an observable side effect.
type Solver = ProblemSpec -> Either CodegenFunError [Asm]
--The solver used by the compiler.
solveProblemSpec :: Solver
solveProblemSpec = incorrectSolver
--A placeholder for testing the rest of the compiler.
incorrectSolver :: Solver
incorrectSolver _ = Right [Comment "Opcodes go here :)"]
--The simplest solver runs ops in some topological order, duplicating all of
--their arguments. That's still not that simple, as once it's done running ops
--it needs to stack shuffle to reach the target.
--That's complicated by vars potentially occurring several times, meaning
--BBs with no ops are not just a combination of popping garbage and permuting.

--Treegraph solver:
--First partition ops into a treegraph, a forest of op trees with a DAG
--of dependencies between them.
--An op tree consists of a root with 0 or >1 user ops and nodes with exactly
--1 user. o1 uses o2 iff o2 returns x and o1 has x in its args, or if
--o2 is in o1's state deps. Note it may use x repeatedly while still
--counting as a single user.
--Leaves are vars returned by the root op of other trees; note a node op
--such as push or gas may have no leaves.
--Each tree depends on the trees whose root op vars it uses, as well as
--all root ops any node has a state dependency on.
--Trees are indexed by root op ID (an Int).
--Trees must be run in some topological order; ideally one would search for
--the best one, but for now I will simply select an arbitrary order.
--All trees must be run, even those which return no var and which no other
--tree depends on (e.g. an mstore); dead ops have already been pruned in Opt.

--Treegraph simplifies codegen by reducing the problem of choosing which op
--to run to choosing which tree to run; internally, tree ops are run in
--right-to-left DFS order and the stack shuffling for each op is done in
--isolation. However, the BB stack scheduling problem is
--more general than that presented in the treegraph paper (Park et al) since
--the BB starts with a nonempty stack and may have a stack target of length >1.
--Consequently, treegraph is not optimal: one can save gas by running ops in
--non-tree order, e.g. running unary ops as soon as their last-use argument
--is ToS or "fishing" a last-use var x to the ToS by pushing the var y which
--is in its position in the target, then swapping y into place.
--My treegraph also requires additional logic for reaching the stack target
--from a given source when there are no ops left to run.
--Important performance improvements TODO:
--1) Make use of target for scheduling trees,
--e.g. if target = x:rest, rest doesn't depend on x and x doesn't
--last-use anything in x, then x can be evaluated last.
--2) Exploit commutativity and associativity of ops.
newtype Treegraph = TG (IntMap (OpTree, Set Int))
  deriving (Eq,Ord,Read,Show)
--Node children should not be [OpTree] since the var returned by a
--child tree may be used several times. Furthermore, a tree may be a
--child due to a state dependency without having its return var (if any) used
--at all.
--A valid tree must have a root node; it cannot be just a leaf.
--Var leaves are in fact not required since the OpSpec contains the args list.
data OpTree = Node OpSpec (Set OpTree)
  deriving (Eq,Ord,Read,Show)
--Partitioning ops into a treegraph:
--Compute the depgraph : IntMap (Set Int)
--Reverse it to get the parent graph : IntMap (Set Int)
--Ops with #parents /= 1 become roots; recursively explore to get their trees.
partitionIntoTreegraph :: ProblemSpec -> Treegraph
partitionIntoTreegraph PS{psOps = ops, psVar2Op = v2op} =
  let children =
        IM.map (\opspec ->
                   let vs = osArgs opspec
                       ns = S.fromList [n |
                                        Just n <- map (flip M.lookup v2op) vs]
                   in S.union ns $ osStateDeps opspec) ops
      parents = invert children
      roots = IM.keysSet $ IM.filter ((/=1) . S.size) parents
      --When building trees, root nodes should not be followed
      --TODO opt...
      rootset = S.fromList $ IS.elems roots
      follow = IM.map (`S.difference` rootset) children
      trees = IM.fromSet (explore follow ops) roots
      --t1 depends on t2 iff:
      --one of its ops:
      -- refers to a v s.t. v2op[v] = t2, or
      -- contains t2 in its state deps
      withDeps = IM.map (addDependencies rootset) trees
  in TG withDeps
  where
    invert :: IntMap (Set Int) -> IntMap (Set Int)
    invert n2ms =
      foldr (uncurry insertSet) IM.empty $ do
      (n,ms) <- IM.toList n2ms
      m <- S.toList ms
      return (m,n)
      {-foldr (\(n,set) m2ns ->
               let ms = S.toList nset
               in foldr (\m m2ns ->
                           insertSet m n m2ns)
                  m2ns ms)
      IM.empty
      n2ms-}
    insertSet :: Int -> Int -> IntMap (Set Int) -> IntMap (Set Int)
    insertSet k v = IM.alter (Just . maybe (S.singleton v) (S.insert v)) k

    explore :: IntMap (Set Int) -> IntMap OpSpec -> Int -> OpTree
    explore follow ops node =
      let Just opspec = IM.lookup node ops
          Just ns = IM.lookup node follow
          trees = S.map (explore follow ops) ns
      in Node opspec trees

    addDependencies :: Set Int -> OpTree -> (OpTree, Set Int)
    addDependencies rootset tree =
      (tree, 
       S.unions $ map (depsOp rootset) $ linearize tree)
    linearize :: OpTree -> [OpSpec]
    linearize (Node opspec trees) =
      opspec : do
      tree <- S.toList trees
      linearize tree
    --The interesting deps of an op, i.e. deps intersected with tree roots.
    --Note v2op is in scope from partitionIntoTreeGraph's lhs.
    depsOp :: Set Int -> OpSpec -> Set Int
    depsOp rootset OS{osArgs=args, osStateDeps=stateDeps} =
      let stackDeps = S.fromList [n | Just n <- map (flip M.lookup v2op) args]
      in S.union stackDeps stateDeps `S.intersection` rootset

treegraphSolver :: Solver
treegraphSolver ps@PS{psSource = src, psVar2Op = v2op, psTarget = tar} =
  let tg = partitionIntoTreegraph ps
  in treeGraphSolver2 v2op src tar tg
--The treegraph solver selects some topological order and returns the result
--of running the trees in that order ++ stack shuffling code to reach the
--target from the resulting stack.
--FW: select among several topological orders. Each tree run gives feedback:
--the stack shuffling overhead + a resulting stack which could be compared vs
--the target.
--Invariant: every var in target either remains on the stack or is produced
--by a tree that hasn't yet been run.
treeGraphSolver2 :: Map String Int -> [String] -> [String] -> Treegraph ->
  Either CodegenFunError [Asm]
treeGraphSolver2 v2op src tar tg = error "todo"

--Need a monad; it can be specialized for treegraph by stacking a var =>
--uses remaining | in_target map State on top of it.
--Error: StackError (which includes compiler errors due to bugs in the solver,
--not just dup and swap out of range).
--Write: [Asm]
--State: the stack. It needn't retain the typeOfVar.
newtype Stack a = Stack {
  unStack :: WriterT [Asm] (StateT [String] (Except StackError)) a
  }
  deriving (Functor,Applicative,Monad,MonadError StackError)
--I don't really want to expose MonadError, but I must to keep dupVar and
--swapVar out of MonadStack while still allowing them to give informative
--errors. Unsatisfactory solution: defined throwStackError.
runStack :: Stack a -> [String] ->
  Either StackError (a,[String],[Asm])
runStack stk vs =
  case runExcept $ flip runStateT vs $ runWriterT $ unStack stk of
    Left err -> Left err
    Right ((a,asm),vs) -> Right (a,vs,asm)
data StackError = BadArgDup Int Int
                -- ^ As distinct from CodegenFunError's DupOutOfRange,
                --which is triggered if the var to dup is on the stack,
                --but at a depth DUP* can't reach.
                | BadArgSwap Int Int
                | BadArgPop --can't pop and empty stack!
                | BadArgOp PrimOp [String]
                --Not a compiler error: wrap a CodegenFunError to be passed
                --up to Solver
                | CGFE CodegenFunError
                --Compiler error: attempting to dup or swap a var not on the
                --stack.
                | DupNonexistent String
                | SwapNonexistent String
  deriving (Eq,Ord,Read,Show)
class Monad m => MonadStack m where
  dup :: Int -> m ()
  swap :: Int -> m ()
  pop :: m ()
  --Fails if the args are not ToS; does not check that the arg and ret arity
  --matches the primop, ignores state deps.
  emitOp :: OpSpec -> m ()
  getStack :: m [String]
  --Note putStack is not exposed.
  --Defining a Stack-specific throwError to avoid FlexibleContexts.
  throwStackError :: StackError -> m a
instance MonadStack Stack where
  --Note: this function is 0-indexed, while EVM DUP* is 1-indexed.
  --dup 0 therefore emits DUP1.
  dup ix = Stack $ do
    vs <- get
    let len = length vs
    case () of
      --dupVar intercepts ix > 15 and throws a CodegenFunError instead.
      _ | ix < 0 || ix > 15 || ix >= len -> throwError $ BadArgDup len ix
        | let -> do
            tell [Opcode $ "dup" ++ show (ix+1)]
            put $ (vs !! ix) : vs
  --swap is also 0-indexed; swap 0 is a noop. EVM SWAP* is 0-indexed,
  --but has no SWAP0 instruction.
  swap ix = Stack $ do
    vs <- get
    let len = length vs
    if ix > 0 || ix > 16 || ix >= len
      then throwError $ BadArgSwap len ix
      else do let a:vs' = vs
                  pre = take (ix-1) vs'
                  b:post = drop (ix-1) vs'
              tell [Opcode $ "swap" ++ show ix]
              put $ b:(pre++a:post)
  pop = Stack $ do
    vs <- get
    case vs of
      [] -> throwError BadArgPop
      v:vs' -> do
        tell [Opcode "pop"]
        put vs'
  emitOp OS{osArgs = args,
            osRet = mret,
            osOp = primop
           } = Stack $ do
    let len = length args
    vs <- get
    let argvs = take len vs
        rest = drop len vs
    if argvs /= args
      then throwError $ BadArgOp primop args
      else do
      tell $ case primop of
               Op op -> [Opcode op]
               Core.RestrictedCore.Push ser ->
                 error "todo"
      put $ [r | Just r <- [mret]] ++ rest
  getStack = Stack get
  throwStackError err = Stack $ throwError err
instance (MonadTrans t, MonadStack m) =>
  MonadStack (t m) where
  dup = lift . dup
  swap = lift . swap
  pop = lift pop
  emitOp = lift . emitOp
  getStack = lift getStack
  throwStackError = lift . throwStackError
--Unlike swap, it doesn't matter which var we dup.
--Throws a CFGE if v is out of range; throws a compiler error if it's not on
--stack at all.
dupVar :: MonadStack m => String -> m ()
dupVar v = do
  vs <- getStack
  case elemIndex v vs of
    Nothing -> throwStackError $ DupNonexistent v
    Just ix
      | ix > 15 -> throwStackError $ CGFE $ DupOutOfRange v ix
      | let -> dup ix
--v may occur at multiple indices on the stack; this swaps with the first
--occurrence. NB: between op execs in treegraph, there are no repeated
--occurrences.
swapVar :: MonadStack m => String -> m ()
swapVar v = do
  vs <- getStack
  case elemIndex v vs of
    Nothing -> throwStackError $ SwapNonexistent v
    Just ix
      | ix > 16 -> throwStackError $ CGFE $ SwapOutOfRange v ix
      | let -> swap ix
  
--Now we have a Stack monad that can be used by any solver!
--Extending it for treegraph:
--TGStack tracks uses remaining for each var; presence in target counts as a
--use.
--When it runs an op, the use counts of each argument op must be decremented.
--Note: that's once for each var in the set of arguments, not once per entry in
--the list!
--When a var has 0 remaining uses, it's garbage and should be popped
--eventually. If it has 1 remaining use and is used as an arg, it should be
--swapped to ToS before duplicated args are pushed.
newtype TGStack a = TGStack {unTGStack :: StateT (Map String Int) Stack a}
  deriving (Functor,Applicative,Monad,MonadError StackError,
            MonadState (Map String Int), MonadStack)
getUseCount :: String -> TGStack Int
getUseCount v = do
  mn <- gets $ M.lookup v
  case mn of
    Nothing -> error "!?"
    Just n -> return n
decUseCount :: String -> TGStack ()
decUseCount v = do
  mn <- gets $ M.lookup v
  case mn of
    Nothing -> error "!?"
    Just 0 -> error $ "Attempted to decrement 0-use var " ++ v
    Just n -> modify $ M.insert v $ n - 1
  
--Run a tree:
--The node has children due to stack and/or state dependency; they may be
--run in any order.
--First run the children which have no stack dependency (their results, if
--any, will be popped).
--Then run the rest in reverse order of occurrence of their result in
--args.
--Now the necessary vars for the node's op will be on the stack; run the op.
runTree :: OpTree -> TGStack ()
runTree (Node opspec trees) = do
  --Inefficiency: I now need to reconstruct the relation var => tree.
  let argset = S.fromList $ osArgs opspec
      --Those trees on which opspec has a stack dependency, indexed by the
      --var they return:
      arg2tree = M.fromList $ do
        tree <- S.toList trees
        let Node chop chs = tree
        case osRet chop of
          Nothing -> []
          Just v ->
            if S.member v argset
            then return (v,tree)
            else []
      --The remaining trees:
      nostackdep = S.filter (\(Node chop _) ->
                               case osRet chop of
                                 Nothing -> True
                                 Just v -> not $ S.member v argset) trees
  
  --We can run those immediately.
  mapM_ runTree $ S.toList nostackdep
  --We're left with trees on which opspec has a stack dep, which must be run
  --in order of *first* appearance in reversed args.
  mapM_ runTree $
    map (\v ->
            case M.lookup v arg2tree of
              Nothing -> error "!?"
              Just tree -> tree) $ nub $ reverse $ osArgs opspec
  --Now the necessary vars for the root op are somewhere on the stack; run it.
  runOp opspec

--Run an op:
--Precondition: its args are somewhere on the stack.
--Invariant: between op exec, there are no duplicate vars o.t.s.
--Naive algo: identify longest suffix of last-use vars o.t.s, dup the rest,
--emit the op.
--Improvement: if all last-use vars are ToS, you can dup and swap in a
--careful order to get optimal code. Swap to get them ToS!
--That solves the x,c2..c7,c1; op:CALL(c1..c7) issue - you get 1 swap instead of
--7 dups followed by pops.
--If the result is garbage, pop it.
--Resulting postcondition: op exec does not leave additional garbage o.t.s.,
--though there may already be garbage there from the lhs.
runOp :: OpSpec -> TGStack ()
runOp opspec = do
  --Dup and swap the op's args to the ToS:
  gatherArgs $ osArgs opspec
  --Emit the op and decrement the use counts of its args:
  tgEmitOp opspec
  --If the var returned is garbage (which can occur without the op being dead
  --for e.g. CALL), pop it and any garbage under it.
  popGarbage
--First identify which vars are last-use and ensure they're ToS.
--Naive approach: in order of use. What is the optimal order?
--Then dup and swap to add rest.
--Special case: only suffix last-use (covers all and none) and no duplicate
--use. Then just need to gather in suffix order (which gatherLastUse will
--already do since it's order of use) and dup.
--The general solution is still necessary and should not need any special
--handling of that case.
gatherArgs :: [String] -> TGStack ()
gatherArgs vs = do
  vns <- mapM (\v -> (,) v <$> getUseCount v) vs
  let lastUse = nub $ map fst $ filter ((==1).snd) vns
  --Swap last-use vars to ToS in order of first use:
  --Stack: lastUse ++ rest
  gatherLastUse lastUse
  --Dup and swap to get vs ++ rest
  gatherDupSwap lastUse vs
--Precondition: each var (and consequently each last-use var) has exactly one
--instance on the stack.
--That is preserved.
--That means a fixed permutation is necessary, so the general optimal
--permutation algo can't be beat.
--Algo: find the permutation, pass it to permute.
--Worst-case cost: 3n, where n is the number of last-use vars to move ToS.
--That's because permute cost <= 3n/2 in total number of elements to permute,
--which is 2n in the worst case.
--It's an open question whether just duping everything but the last-use
--suffix already on the stack is better; TODO try both.
gatherLastUse :: [String] -> TGStack ()
gatherLastUse vs = error "todo"

--Stack: last-use variables lu ++ rest; we will not modify rest.
--Special case: lu is a suffix of vs; in that case only dup.
--Precondition: lu has no duplicates; that is not preserved.
--Vars in correct position should not be touched.
--lu is in order of first use, so if it's to be permuted then |vs| > |lu|.
--Strategy: when the next var needs to be dup'd, do so.
--Note the vars from lu may occur repeatedly in the target, so instances of
--them may need to be dup'd.
--Latent permutation: arrows into the stack which hasn't been pushed yet =>
--dup the source's ultimate value and swap it.
gatherDupSwap :: [String] -> [String] -> TGStack ()
gatherDupSwap lu vs = error "todo"

tgEmitOp :: OpSpec -> TGStack ()
tgEmitOp opspec = error "todo"
--Pops any garbage ToS
popGarbage :: TGStack ()
popGarbage = getStack >>= go
  where go vs =
          case vs of
            [] -> return ()
            v:vs' -> do
              b <- isGarbage v
              if b
                then pop >> go vs'
                else return ()
isGarbage :: String -> TGStack Bool
isGarbage v = (== 0) <$> getUseCount v

--Finally shuffle the stack to meet the target; may involve popping garbage,
--swapping and duping.
--Always swapping last-use vars in op exec will *not* avoid the need to pop
--garbage, since a BB may have no ops and garbage in its lhs.
--Nor does it avoid garbage ToS, since runOp may never run.
--Precondition: no duplicate vars on stack.
--Naive algo:
--While there is garbage:
-- if ToS: pop it
-- else: swap it to top
--Now there is no garbage, and still no duplicates. The stack length is <=
--the target length. From now on, we only dup and swap.
--That's exactly the same problem as gatherDupSwap!
finalShuffle :: [String] -> TGStack ()
finalShuffle target = error "todo"

--Efficient GC: if you have a single non-garbage var ToS and a run of garbage
--under, it's efficient to swap with the deepest garbage in the run possible.
--In general, you need n swaps to move n non-garb below a run; doing so
--shortens the run length since you must interleave the swaps with pops.

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
