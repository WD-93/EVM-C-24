{-# LANGUAGE LambdaCase #-}
module Stack where

import qualified Data.Set as S
import Data.Set (Set(..))
import qualified Data.Map as M
import Data.Map (Map(..))
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow ((***))
import Data.List (elemIndex)
import Control.Monad.Reader
import Control.Monad.Trans.Except --for Stack
import Data.Maybe (fromMaybe)

import DTs
import qualified IR1 (Operator(Opcode)) --Opcode conflicts with Asm
import IR1 hiding (Operator(Opcode))
import ToyCFG
import Asm

--Now that we have a simplified CFG, it's time to implement stack scheduling
--for the SLCs and branch between them efficiently.
--Codegen state: [SSAName], use counts per var.
--For now, do not exploit commutativity in commutative ops or reduce.
--Every var maps to a [var], optree<live vars>
--For now, no identical subtree merging. It might not always be efficient,
--consider repeated calls to a fun.
--Ops emitted in reverse DFS order. Map vars to ops; each var in rhs -> an
--edge to the corresponding op.
--If truly empty SLCs (no substs, no jumpi, no ops) remain, map them to their
--follow-up.

--First, really inefficient version: a jumpdest for every SLC, no
--fallthroughs.
--Then every SLC can be emitted independently in a mapM.
--No, I'll fallthrough AMAP.

--If the then branch but not the else branch of a jumpi can be fallen through
--to, negate the cond with an iszero?
--That doesn't avoid the jumpi, but if stack adjustment is required you can
--avoid a subsequent jump.
--If there's one edge to the else branch of a jumpi, you can set the layout
--to be exactly the end of the ops - garbage included.

--SLC2 => asm
--If rc > 1, it's the target of a jumpi then case, or it's the entrypoint,
--place a jumpdest.
--If no jumpdest, no need to place a label.
--Label naming scheme:
--fname => fname.entrypoint
--label n of fname => fname.label<n>
--In case future CFGs might jump back to the entrypoint, place both
--fname.entrypoint and fname.label.

--Structure of a compiled SLC:
--ops, branch code
--Structure of branch code:
--jump lab: stack adjustment to layout lab, jump | fallthrough
--return: stack adjustment to $ret:returned words, jump
--jumpi v th el:
--lth, lel <- layouts of th and el
--Look at refcounts too
--If the lives are equal and the layout of one is free, you can share the
--stack shuffling code.
--Better yet: if one branch has a live which is a superset of the other,
--make that the then branch, adjust the stack to its live, then jumpi.
--Stack adjustment for the else branch is "free" - it doesn't require an
--additional jump to do.
--If the lives are unequal but neither is a strict superset of the other
--(i.e. both have vars not present in the other), the extra stack-aware SLC
--generated for stack shuffling the then branch can still fall through to the
--then branch; treat it as an ordinary SLC.
--Problem: I must generate an ID for it. Hack: start from -1...
--Opt: if two SLCs are identical (in content and branch), you can unify them.
--Hold on... due to renaming, you may get repeated vars in the layout.
--The flexibility from having multiple instances of the same var grants room
--for opt in the else branch code.

--A truly empty SLC is characterized by no stack ops, followed by a jump;
--instead of placing it, add it to the map.
--Note it may alter scope by renaming vars.
--After mapping to a canonical label, a label is either unplaced, placed and
--at the head of one of the lists, or in one of the lists.

--Each op has input and output words; vars of IRT type Word {} are stack
--words, the rest are virtual.
--The SSAOp does not contain info on the type of rhs vars; consequently that
--must be tracked in the SLC to asm monad.

--Finally, compilation to asm:
--Only string errors for now
--For now, only modules with a main are accepted.
--The other functions are all placed (no tree shaking here) in ascending of
--name.
compile2asm :: Map Name (ToyCFG.Label,CFG2) -> Either String [Asm]
compile2asm nm2def =
  case M.lookup "main" nm2def of
    Nothing -> Left "Missing main in compile2asm"
    Just maindef -> do
      asm <- def2asm "main" maindef
      asms <- mapM (\(f,def) -> def2asm f def) $
              M.toList $ M.delete "main" nm2def
      return $ asmPrologue ++ concat (asm:asms)
--Note compilation of a function, including main, need not place the entrypoint
--SLC first in the generated asm!
--Furthermore, main is an ordinary function which must take a return address
--and will jump to it on return. That means we need a prologue which handles
--that. The prologue assumes main takes () as an argument.
asmPrologue :: [Asm]
asmPrologue = [
  PushLabel 2 (LNamed "$exitCall"),
  PushLabel 2 (LNamed "main"),
  Opcode "jump",
  PlaceLabel (LNamed "$exitCall"),
  Opcode "jumpdest",
  Opcode "stop"
              ]

--Compiles a function definition to a contiguous blob of assembly.
--Compiles SLCs in DFS order from entrypoint, which always has a jumpdest and
--also places the label f.
--The order determines which SLCs will fall through to their continuation;
--earlier ones are preferred.
--The entrypoint has a fixed layout: $ret,$anon0..$anonN
--Note that means no other SLC should jump to it for now... and thankfully
--they don't.
--The layout includes only stack vars. Note it's always set before the SLC
--itself is placed!
--For now, compile ops in the order they appear in SLCs... that'll usually be
--pretty efficient.
--For now, do not allocate additional SLCs for stack adjustment of the then
--branch; instead include all generated asm in the branch asm.
def2asm :: Name -> (ToyCFG.Label,CFG2) -> Either String [Asm]
def2asm f (entrypoint,cfg) = error "TODO"

data StackS = StackS {
  --We assemble them into lists of SLCs that fall through to each other later.
  staxCompiledSLCs :: Map ToyCFG.Label CSLC,
  --The layout of the stack variables from live per SLC
  --Note it's names, not SSANames; SSANames are specific to each source SLC.
  staxLayouts :: Map ToyCFG.Label [Name],
  --Tracks whether one can still fall through to a SLC; if in the set, one
  --cannot.
  staxFallenThroughTo :: Set ToyCFG.Label
  }
     deriving (Eq,Ord,Read,Show)
type Stack = ExceptT String
  (ReaderT (Name,ToyCFG.Label,CFG2) --fname, entrypoint, cfg
  (State StackS))
data CSLC = CSLC {
  cslcOps :: [Asm], --includes branch
  cslcFallthrough :: Maybe ToyCFG.Label
                 }
  deriving (Eq,Ord,Read,Show)
stackGetSLC2 :: ToyCFG.Label -> Stack SLC2
stackGetSLC2 lab = do
  (_,_,cfg) <- ask
  case M.lookup lab cfg of
    Nothing -> throwE $ "LTN in stackGetSLC2: " ++ show lab
    Just slc2 -> return slc2
--First compute use count per var from ops, branch and the live of dests
--(that requires vers and subst to compute)
--Then compile ops, compile branch and finally insert the CSLC into the map
--and recurse on the child labels
compileLabel :: ToyCFG.Label -> Stack ()
compileLabel lab =
  ifM (hasBeenCompiled lab)
  (return ())
  (do (slc,vers,subst,rc) <- stackGetSLC2 lab
      --Get layout, which is guaranteed to have been set earlier
      mlayout <- stackGetLayout lab
      if mlayout == Nothing
        then throwE $ "Layout wasn't set before compiling label " ++ show lab
        else return ()
      let Just layout = mlayout
      --Get function name for disambiguating return address labels
      --The entrypoint is for determining whether to place the fname label
      --and add a mandatory jumpdest.
      (fname,entrypoint,_) <- ask
      --Get use counts; TODO deduplicate code for this
      --For each op: if a var is in rhs, +1
      let ucOps = useCountOps slc
      --For branch: get live vars less $mem, +1 for each non-substituted var
      --Note: when branching, you may need to dup substituted vars!
      ucBranch <- useCountBranch slc vers subst
      let uc = M.unionWith (+) ucOps ucBranch
          (_,opAsm,sos) = runSelectOps (mapM_ selectOps $ slcOps slc) $
                          SOS {sosUsesRemaining = uc,
                               sosLayout = map ((,)0) layout,
                               --Hack: they're all uint256[1] except for $mem 
                               sosVarTypes = M.fromSet
                              (\case (_,"$mem") -> Mem
                                     _ -> tword
                              ) $ S.map ((,)0) $ slcLive slc
                              ,
                               sosLocation = (fname,lab),
                               sosCallCount = 1 --the next UID
                              }
                               
      let startAsm =
            [PlaceLabel $ LNamed fname | lab == entrypoint] ++
            [PlaceLabel $ cfgLabel2AsmLabel fname lab] ++
            --TODO only gen JD if lab == entrypoint, rc > 1 or lab is jumped to
            --from jumpi. Implement using a Boolean parameter.
            [Opcode "jumpdest"]
      --Now to compile branch. This needs to know the starting layout,
      --var types (to remove $mem from return, for example),
      --and the layout + fallthroughability of the branchees
      --It does *not* recursively call compileLabel, so we don't need to add
      --a set of already traversed labels to StackS
      (branchAsm,mfallthrough) <- compileBranch vers subst lab (sosLayout sos)
                                  (sosVarTypes sos) --I could just filter $mem
                                  (slcBranch slc)
      let cslc = CSLC {cslcOps = startAsm ++ opAsm ++ branchAsm,
                       cslcFallthrough = mfallthrough
                      }
      --Insert the CSLC into the compiled set
      modify (\stax -> stax{staxCompiledSLCs =
                               M.insert lab cslc $ staxCompiledSLCs stax})
      --Recurse on the original SLC's children
      mapM_ compileLabel $ slcChildren slc
  )
--This is the trickiest bit in Stack
--The type map is needed to filter the live set
--ver and sub are needed to transform the  targets of branchees
compileBranch :: Map Name Int -> Map SSAName SSAName -> 
                 ToyCFG.Label -> [SSAName] ->
                 Map SSAName IRT -> Branch SSAName ->
                 Stack ([Asm],Maybe ToyCFG.Label)
compileBranch ver sub self layout types branch =
  case branch of
    Jump lab -> do
      --lab's layout is either fixed or free
      --If fixed, we translate its layout to current SSA vars,
      --and adjust to that.
      --If free:
      --First GC garbage by swapping and popping
      --If there are repeated vars, dup them!
      adjustmentOps <- adjustToMaybeTarget ver sub layout lab

      --Finally, the jump or fallthrough:
      --If self == lab || lab is not fallthroughable, jump lab
      --Otherwise, set fallthrough to Just lab and mark lab as fallen through
      --to.
      (br,mft) <- tryFallthrough self lab
      return (adjustmentOps ++ br,mft)
    Jumpi cond th el -> do
      --First: compute the combined live of th, el and the branch
      --Do not adjust to that, instead GC!
      --Why? Consider th has live x and el live y and they both map to the
      --SSA var X. Adjustment will unnecessarily duplicate X, when in either
      --case we only need one!
      --Common case: ifte where th and el have refcount 1.
      --Then they're both free and ftable...
      --Ideally I'd be able to modify the live of th,el to have no cleanup

      --Get live stack vars for both branches
      lth <- S.delete "$mem" <$> liveVars th
      lel <- S.delete "$mem" <$> liveVars el
      --Get layout for both branches
      --Note if they have no layout they're fallthroughable
      mlth <- stackGetLayout th
      mlel <- stackGetLayout el
      --All the different cases...
      --If the SSA lives are equal:
      -- If the layouts are equal:
      --  Adjust to cond:layout
      --  If th is ftable but el is not, iszero and swap the branches
      --  Attempt to fallthrough to the then branch, which is now last.
      
      --No time... just do the inefficient default for now:
      --Do no shared adjustment, instead jumpi (dup cond) to a new then
      --adjustment SLC that may fall through to the then branch.
      --If you didn't jump, adjust to the el layout and try to fall through
      adjustThen <- adjustToMaybeTarget ver sub layout th
      adjThenLabel <- createNewSLC self adjustThen th
      adjThenAsmLabel <- labelToLabel adjThenLabel
      adjustElse <- adjustToMaybeTarget ver sub layout el
      (contToElse,mft) <- tryFallthrough self el
      let (_,dupCond,_) = runStackOps (soDupName cond) layout
      return (dupCond ++
              [PushLabel 2 adjThenAsmLabel] ++
              adjustElse ++
              contToElse
             ,mft)
      --Opt: if th, el have the same layout L, adjust to cond:L and jumpi.
      --If it's possible to fall through to el, do so;
      --If ditto th, iszero and swap branches.

      --If layout th > layout el, adjust to cond:layout th and jumpi
      --then adjust to layout el and possibly fall through
      
    --Filter all non-word vars from vs.
    --Substitution has already been done; vars may be repeated.
    --Precondition: there may be garbage on stack, but each var is unique.
    --Each var in the goal is already present on the stack.
    BReturn vs -> do
      vsW <- filterM (\v ->
                        case M.lookup v types of
                          Just (Word{}) -> return True
                          Just _ -> return False
                          Nothing ->
                            throwE $ "return v has no type in compileBranch: "
                            ++ show v) vs
      let asm = compileReturn layout vsW
      return (asm,Nothing) --It will ofc not fall through to anything

--For brevity
type L = ToyCFG.Label
--A means of allocating new CSLCs without any additional state: since each
--SLC allocates at most one new SLC (in the event of a jumpi then branch to
--a fallthroughable dest), give the new SLC -(lab+1).
--Then both the then and else branch may fall through... though when the
--then branch is a superset of the else branch, it's preferable to adjust to
--it and jumpi directly.
createNewSLC :: L -> [Asm] -> L -> Stack L
createNewSLC from adjustmentAsm to = do
  let newLabel = -(from+1)
  asmLabel <- labelToLabel newLabel
  (branchAsm,mfallthrough) <- tryFallthrough newLabel to
  modify (\stax->stax{staxCompiledSLCs =
                      M.insert newLabel (CSLC{cslcOps =
                                                 [PlaceLabel asmLabel,
                                                  Opcode "jumpdest"] ++
                                                 adjustmentAsm ++ branchAsm,
                                              cslcFallthrough =
                                                 mfallthrough}) $
                      staxCompiledSLCs stax})
  return newLabel

--The layout may be fixed or free; if free we flexibly adjust to the live set
--and mark it fixed. If fixed we adjust the target layout.
adjustToMaybeTarget :: Map Name Int -> Map SSAName SSAName ->
                       [SSAName] -> L ->
                       Stack [Asm]
adjustToMaybeTarget ver sub layout lab = do
  live <- S.delete "$mem" <$> liveVars lab
  mtarget <- stackGetLayout lab
  let (adjustmentOps,mbNewLayout) =
        case mtarget of
          --Fixed
          Just target ->
            let ssaTarget = map (name2SSAName ver sub) target
                (_,w,_) = runStackOps (adjustToTarget ssaTarget) layout
            in (w,Nothing)
          --Free
          Nothing -> let (_,w,nl) = runStackOps
                           (adjustToFlexible ver sub live) layout
                         --Now we have a layout nt which is ambigous:
                         --if x,y,z all map to X, the SSA layout will be
                         --X,X,X.
                         --For each var in live, we assign it to the first
                         --SSA var that matches.
                         newLayout = assignNamesToMatching ver sub live nl
                     in (w,Just newLayout)
  --If the layout was free, set lab's layout to the result of adjustmentOps
  case mbNewLayout of
    Just newLayout -> stackSetLayout lab newLayout
    _ -> return ()
  return adjustmentOps

--Tries to fall through to lab, returning the branch asm and maybe fallthrough
tryFallthrough :: L -> L -> Stack ([Asm],Maybe L)
tryFallthrough self lab = do
  ftable <- isFallthroughable lab
  if self == lab || not ftable
    then do
    asmLab <- labelToLabel lab
    return ([PushLabel 2 asmLab,
             Opcode "jump"], Nothing)
    else do
    markFallenThroughTo lab
    return ([], Just lab)

--First reverse the mapping, obtaining a Map SSAName [Name]
--Then go through the SSA names, popping the first name from the map.
assignNamesToMatching :: Map Name Int -> Map SSAName SSAName ->
                         Set Name -> [SSAName] -> [Name]
assignNamesToMatching ver sub live ssaLayout =
  go revMap ssaLayout
 where
   revMap = foldr (\nm rm ->
                     let k = name2SSAName ver sub nm
                     in case M.lookup k rm of
                          Nothing -> M.insert k [nm] rm
                          Just nms -> M.insert k (nm:nms) rm
                  ) M.empty $ S.toList live
   go rm = \case
     [] -> []
     ssa:ssas ->
       case M.lookup ssa revMap of
         Nothing ->
           error "Something went terribly wrong in assignNamesToMatching"
         Just (nm:nms) ->
           nm : go (M.insert ssa nms rm) ssas
         Just [] -> error "We ran out of names in assignNamesToMatching!?"
markFallenThroughTo :: ToyCFG.Label -> Stack ()
markFallenThroughTo lab =
  modify (\stax -> stax{staxFallenThroughTo = S.insert lab $
                         staxFallenThroughTo stax})
isFallthroughable :: ToyCFG.Label -> Stack Bool
isFallthroughable lab = not <$> S.member lab <$> gets staxFallenThroughTo

stackSetLayout :: ToyCFG.Label -> [Name] -> Stack ()
stackSetLayout lab layout =
  modify (\stax->stax{staxLayouts=M.insert lab layout $ staxLayouts stax})

--For when the target layout is free, requiring only a set of live vars is
--on the stack.
--First, translate the set to a bag of SSA vars; that bag in any order is the
--goal.
--GC out the garbage, i.e. any var not in the bag
adjustToFlexible :: Map Name Int -> Map SSAName SSAName -> Set Name ->
  StackOps ()
adjustToFlexible ver sub live = do
  let bag = count $ map (name2SSAName ver sub) $ S.toList live
      notGarb = M.keysSet bag
  garbageCollect notGarb
  --Now we have only live SSA vars in any order, and a bag of vars we want the
  --stack to sum to. First deduct the live vars from the bag, then for each
  --(var,n >= 0) remaining in the bag, duplicate var n times
  --Note n should not be < 0 if we start with a layout without duplicate vars
  vs <- get
  let bagRem = M.unionWith (+) bag $ M.map negate $ count vs
  mapM_ (\case (var,n)
                 --No point trying to repair here; something must've gone wrong
                 --earlier to violate the precondition.
                 | n < 0 -> error "Oh dear, something went terribly wrong!"
                 | let -> replicateM n $ soDupName var) $ M.toList bagRem
    where count vs = M.unionsWith (+) $ map (flip M.singleton 1) vs
--While true:
--If there's garbage TOS, pop it
--Otherwise, find the bottom garbage var and swap it to the top
--If there is no garbage, break.
--Note if the bottom garbage is beyond index 16, this breaks (TODO fix)
--If there are 17 non-garbage words TOS, this breaks unavoidably unless you
--stash to memory.
garbageCollect :: Set SSAName -> StackOps ()
garbageCollect notGarb = do
  vs <- get
  case vs of
    [] -> return ()
    v:vs
      | garb v -> soPop >> garbageCollect notGarb
      | let -> do
          --TODO do this calculation only once, accounting for pops
          let garbixs = map snd $ filter (\(v,_) -> garb v) (zip vs [1..])
          case garbixs of
            [] -> return ()
            ix:_ -> soSwapIndex ix >> garbageCollect notGarb
    where garb v = not (S.member v notGarb)
--Here, we must dup, swap and pop.
--Iteratively set BOS to the correct word.
--Whenever garbage is TOS, pop it.
--What is garbage? Vars not present in target.
--Vars may be replicated in target; if so you need to dup.
--Simplifying assumption: source and target are <= 16 words so they're all in
--swap/dup range.
{-
Algo:
 Loop invariant:
  stack = {vars}{correctly placed suffix}
  vars may include garbage, but has at most one replica of each var
  therefore if the next var to place is in suffix, you must dup+swap
 proceeding from ix = BOS to TOS: --note BOS index may change
  v = last(target)
  if stack[ix] == v:
   continue
  else if v is in suffix:
         dup v, swap to stack[ix]
       else swap v to top, then to stack[ix]
  target = init target
Edge case: x => (x,x,x)
x is already BOS, but the other two x's must be dup'd.
When duping, they're put in the right position and you don't need to swap.
-}
adjustToTarget :: [SSAName] -> StackOps ()
adjustToTarget target = do
  let notGarbage = S.fromList target
  adjustToTarget' notGarbage (length target) S.empty 0 (reverse target)
adjustToTarget' :: Set SSAName -> --not garbage
                   Int -> --length of target
                   Set SSAName -> --names already in the suffix
                   Int -> --the index off BOS to swap to
                   [SSAName] -> --names to place remaining
                   StackOps ()
adjustToTarget' notGarbage targetLen suffixVars i = \case
  --The stack is now {garbage}{target}; pop the garbage
  [] -> do
    len <- gets length
    replicateM_ (len-targetLen) soPop
  --The stack is {prefix}{suffix of target}
  --Prefix may be empty; if so just dup the remaining vars
  --Prefix is empty when i >= length of stack
  --Pop garbage before the emptiness check
  v:vs -> do
    soPopGarbage notGarbage
    len <- gets length
    if i >= len
      --Just dup the rest
      then mapM_ soDupName (v:vs)
      else do
      --The top word is not garbage, nor does it occur in suffix
      --One might think it would be efficient to swap it to its correct
      --position now, but that may not be possible if it's to be placed to
      --the left of the current TOS.
      --Instead, we extend the suffix.
      w <- soGetNameBOS i --this is guaranteed to succeed
      if v == w
        then return ()
        else do
        --If v is in suffixVars, dup it
        --Otherwise, swap it to top.
        if S.member v suffixVars
          then soDupName v
          else soSwapName v
        --Then swap v to correct pos.
        soSwapBOS i
      adjustToTarget' notGarbage targetLen
        (S.insert v suffixVars) (i+1) vs
        
soPopGarbage :: Set SSAName -> StackOps ()
soPopGarbage notGarbage = do
  vs <- get
  case vs of
    v:_ | not (S.member v notGarbage) -> soPop >> soPopGarbage notGarbage
    _ -> return ()
compileReturn :: [SSAName] -> [SSAName] -> [Asm]
compileReturn source target =
  let (_,w,_) = runStackOps (compileReturnM target) source
  in w
compileReturnM :: [SSAName] -> StackOps ()
compileReturnM target = do
  adjustToTarget target
  tell [Opcode "jump"]
--TODO handle failure...
soSwapIndex :: Int -> StackOps ()
soSwapIndex i = do
  tell [Swap i | i > 0]
  modify (swapF i)
--TODO dedup with soDupName
soSwapName :: SSAName -> StackOps ()
soSwapName nm = do
  mi <- gets (elemIndex nm)
  case mi of
    Nothing -> error "Compiler error soSwapName"
    Just i -> soSwapIndex i
soDupIndex :: Int -> StackOps ()
soDupIndex i = do
  tell [Dup i]
  modify (dupF i)
soDupName :: SSAName -> StackOps ()
soDupName nm = do
  mi <- gets (elemIndex nm)
  case mi of
    Nothing -> error "Compiler error soDupName"
    Just i -> soDupIndex i
dupF :: Show a => Int -> [a] -> [a]
dupF i as =
  case as !? i of
    Nothing -> error $ "OOB in dupF: " ++ show (i,as)
    Just a -> a:as
soGetNameIndex :: Int -> StackOps SSAName
soGetNameIndex i = do
  mnm <- gets (!? i)
  case mnm of
    Nothing -> error "Compiler error soGetNameIndex"
    Just nm -> return nm
soGetNameBOS :: Int -> StackOps SSAName
soGetNameBOS i = do
  bos <- soBOS
  soGetNameIndex (bos - i)
--The swap index of BOS
soBOS :: StackOps Int
soBOS = (\n -> n - 1) <$> gets length
--Swap off BOS; 0 => swap to BOS, 1 => one closer to TOS etc.
--Has the advantage indices remain fixed as you dup and pop.
soSwapBOS :: Int -> StackOps ()
soSwapBOS i = do
  bos <- soBOS
  soSwapIndex (bos - i)
--TODO error handling
soPop :: StackOps ()
soPop = tell [Opcode "pop"] >> modify tail

--For codegen of branches, which only need to gen dup/swap/pop, jump/i and
--placelabel + jumpdest.
--TODO deduplicate with SelectOps.
type StackOps = WriterT [Asm] (State [SSAName])
runStackOps :: StackOps a -> [SSAName] -> (a,[Asm],[SSAName])
runStackOps so nms =
  let ((a,w),s) = runState (runWriterT so) nms
  in (a,w,s)
      
labelToLabel :: ToyCFG.Label -> Stack Asm.Label
labelToLabel lab = do
  (fname,_,_) <- ask
  return $ cfgLabel2AsmLabel fname lab
cfgLabel2AsmLabel fname lab = LNamed $ fname ++ ".label" ++ show lab
  
useCountOps :: SLC SSAName -> Map SSAName Int
useCountOps slc =
  let ops = slcOps slc
      rhses = map (\(_lhs,_op,rhs) -> rhs) ops
      varsets = map S.fromList rhses
  in M.unionsWith (+) $ map (M.fromSet (const 1)) varsets 
--Does the jump cond need to be considered a separate use?
--It doesn't matter for op generation, but if I want to reuse the SelectOps
--monad for branches... no, I can recover that info later.
--Note when I do, location and call count are irrelevant and can be undefined.
useCountBranch :: SLC SSAName -> Map Name Int -> Map SSAName SSAName ->
  Stack (Map SSAName Int)
useCountBranch slc ver sub = do
  let labs = slcChildren slc
  live <- S.unions <$> mapM liveVars labs
  let liveSSAs = S.map (name2SSAName ver sub) live
      usedBranch = case slcBranch slc of
                     Jumpi cond _ _ -> S.singleton cond
                     BReturn vs -> S.fromList vs
                     Jump _ -> S.empty
  return $ M.fromSet (const 1) $ S.union usedBranch liveSSAs

--TODO use earlier/deduplicate
name2SSAName :: Map Name Int -> Map SSAName SSAName -> Name -> SSAName
name2SSAName ver sub nm =
  let ssanm = (fromMaybe 0 (M.lookup nm ver), nm)
      canonical = fromMaybe ssanm (M.lookup ssanm sub)
  in canonical
  
hasBeenCompiled :: Int -> Stack Bool
hasBeenCompiled lab = M.member lab <$> gets staxCompiledSLCs
--May include non-stack vars (well, one: $mem)
liveVars :: Int -> Stack (Set Name)
liveVars lab = slcLive <$> slc2ToSLC <$> stackGetSLC2 lab
--Get the layout of a SLC
--Oh dear: given a layout with SSA vars, need to apply the inverse of
--name2SSAName. One SSA var may become multiple names.
--FW: when you branch to a 1-edge (in an ifte if CFG opt works correctly),
--apply the subst map to the branchee's ops.
--For now, always duplicate if one SSA var => multiple vars in live.
stackGetLayout :: ToyCFG.Label -> Stack (Maybe [Name])
stackGetLayout lab =
  M.lookup lab <$> gets staxLayouts

--SelectOps state
data SOS = SOS {
  --1 per op using v + 1 if live at branch + 1 if branching on it
  sosUsesRemaining :: Map SSAName Int,
  --The vars on stack, may include garbage
  sosLayout :: [SSAName],
  --The type of each var bound so far; because I haven't propagated type info
  --in live, I instead hackily declare the first $mem to be Mem and the rest
  --to be uint256 when initializing.
  sosVarTypes :: Map SSAName IRT,
  --Function and label ID should really be in Reader; TODO change
  sosLocation :: (Name,ToyCFG.Label),
  --Call count gives each call return address a UID for label generation
  sosCallCount :: Int
  }
  deriving (Eq,Ord,Read,Show)
                
type SelectOps = WriterT [Asm] (State SOS)
runSelectOps :: SelectOps a -> SOS -> (a,[Asm],SOS)
runSelectOps sel sos =
  let ((a,w),s) = runState (runWriterT sel) sos
  in (a,w,s)
--The ops plural referred to here are stack adjustment ops
--(swap,dup,pop) and the "payload" op, such as add or Call.
selectOps :: SSAOp -> SelectOps ()
selectOps (lhs,op,rhs) = do
  popTOS
  --Take only stack vars from lhs and rhs; virtual vars such as Mem have no
  --runtime impact.
  let onlyWords vts = do
        (var,t) <- vts
        case t of
          Word {} -> [(var,t)]
          _ -> []
      lhsW = onlyWords lhs
  rhsW <- map fst <$> onlyWords <$> mapM (\v -> do
                                             t <- varType v
                                             return (v,t)) rhs
  --Find longest suffix of last-use vars in the RHS and swap them to top
  (prefix,suffix) <- splitRHS rhsW
  swapToTop suffix
  --Dup the rest
  dupToTop prefix
  --Emit the Operator compiled to asm, removing the args from stack and
  --pushing the lhs with the given types.
  --FW: optimize codegen for reduce; whenever two last-use args to the reduce
  --are TOS, you should reduce them - before placing the args TOS!
  emitOperator lhsW op rhsW
  popTOS

emitOperator :: [(SSAName,IRT)] -> IR1.Operator -> [SSAName] ->
  SelectOps ()
emitOperator lhs op rhs = do
  --First, remove rhs from TOS
  vs <- getLayout
  setLayout $ drop (length rhs) vs
  --Emit the "payload code" for the operator
  --the length rhs param is currently needed for reduce; in future reduce
  --will do its own arg swapping.
  emitPayload (length rhs) op
  --Decrement the use count of each unique var in rhs
  mapM decrementUses $ S.toList $ S.fromList rhs
  --Finally, add lhs to TOS and varTypes
  mapM_ (\(var,t) -> do
           vs <- getLayout
           setLayout (var:vs)
           setVarType var t
        ) $ reverse lhs
emitPayload :: Int -> IR1.Operator -> SelectOps ()
emitPayload arglen = \case
  --Oh no: because I don't record size info in const, -1 becomes 32B
  IR1.Push (Const n) -> do
    let blen n | n < 0 = 32
               | n == 0 = 0
               | n > 0 = 1 + blen (n `div` 256)
    tell [Asm.Push (blen n) n]
  --The function f's label is just "f"... is that OK?
  IR1.Push (LabelConst nm) -> tell [PushLabel 2 $ LNamed nm]
  IR1.Opcode opcode -> tell [Opcode opcode]
  --Inefficiency: f is already TOS, but now I push the return address and
  --swap it. In future I need to get to ret:args:rest, then dup f.
  --Better stack planning is possible...
  Call -> do
    ret <- newReturnAddress
    tell [
      PushLabel 2 ret,
      Swap 1,
      Opcode "jump",
      PlaceLabel ret,
      Opcode "jumpdest"
      ]
  Reduce opcode -> sequence_ [tell [Opcode opcode] | _ <- [1..arglen-1]]

--Allocates a new label for the return address to a call
--Format: f.label<slcLab>.ret<callCount>
newReturnAddress :: SelectOps Asm.Label
newReturnAddress = do
  (f,slcLab) <- gets sosLocation
  n <- gets sosCallCount
  modify (\sos->sos{sosCallCount=n+1})
  return $ LNamed $ concat [f,".label",show slcLab,".ret",show n]

--TODO refactor code with Control.Monad.Extra, Control.Monad.Loops
--Alt: place these defs deeper in my module tree so I can make better use of it.
takeWhileM :: Monad m => (a -> m Bool) -> [a] -> m [a] 
takeWhileM f =
        \case [] -> return []
              x:xs ->
                ifM (f x)
                ((x:) <$> takeWhileM f xs)
                (return [])
ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM mb th el = do
  b <- mb
  if b
    then th
    else el
--rhs => (prefix to dup, last-use suffix to swap and consume)
--To simplify swapToTop, we stop accumulating the suffix when we encounter a
--var for the second time. The suffix will therefore contain at most one
--instance of any var.
splitRHS :: [SSAName] -> SelectOps ([SSAName],[SSAName])
splitRHS vs = do
  suffix_ <- takeWhileM isLastUse (reverse vs)
  --End the suffix at the first duplicate
  let suffix = reverse $ takeUntilDuplicate suffix_
  --I could optimize this with a takeDrop function, but no matter for now
  let prefix = take (length vs - length suffix) vs
  return (prefix,suffix)
  where takeUntilDuplicate = tud S.empty
        tud s =
          \case
            x:xs
              | not (S.member x s) -> x : tud (S.insert x s) xs
            _ -> []
--Precondition: all the names are in the layout; there is only one instance of
--each name on the stack.
--Swaps nms to TOS in that order; emits only swap instructions, does not
--take the opportunity to collect garbage.
--Problem: last-use refers to #ops, not #instances within an op.
--The last-use suffix could be (x,x), for example.
--Temporary solution: stop accumulating the suffix when a var is encountered
--for the second time.
{-
Swapping algo:
Iterate over the nms in reverse order
Swap each name to its appropriate position (length nms - 1..0)
Index 0 is a special case, because you need to emit at most one swap.
-}
--Note this algo wouldn't work if the suffix contained repeated vars, because
--when a var is encountered for the second time it'll swap the var away from
--where it was placed previously.
--It also clearly wouldn't work because it performs no dups, which duplicate
--vars require...
swapToTop :: [SSAName] -> SelectOps ()
swapToTop nms = do
  let nmposs = reverse $ zip nms [0..]
  mapM_ swapToPos nmposs
--Is nm already at i? Then we're done.
--Otherwise, swap it to TOS and then to i.
swapToPos (nm,i) = do
  mnm' <- indexName i
  case mnm' of
    Nothing -> error "Compiler error: this shouldn't happen"
    Just nm'
      | nm == nm' -> return () --we're done
      | let -> do
        swapName nm
        swapIndex i
swapName :: SSAName -> SelectOps ()
swapName nm = nameIndex nm >>= swapIndex
swapIndex :: Int -> SelectOps ()
swapIndex = \case
  0 -> return () --it's a noop
  i | i < 0 || i > 16 -> error $ "Compiler error: swapIndex OOB " ++ show i
    | let -> do
        tell [Swap i]
        vs <- getLayout
        --A swap to an index outside the layout's range should never be
        --attempted by the compiler
        if length vs - 1 < i
          then error $ "Compiler error: swapIndex OOB " ++ show (i,vs)
          else setLayout (swapF i vs)
--Handles computing the swapped layout
--Also used in the StackOps monad
swapF :: Int -> [a] -> [a]
swapF i (pre:vs) =
  let (post,vs') = swapF' i pre vs
  in post:vs'
swapF' :: Int -> a -> [a] -> (a,[a])
swapF' 1 pre (post:vs) = (post,pre:vs)
swapF' i pre (v:vs) =
  let (post,vs') = swapF' (i-1) pre vs
  in (post,v:vs')

--Gets the first index where a name is present
nameIndex :: SSAName -> SelectOps Int
nameIndex nm = do
  mi <- elemIndex nm <$> getLayout
  case mi of
    Nothing -> error $ "Compiler error: nameIndex <missing nm> " ++ show nm
    Just i -> return i
--Gets the name at a particular index, Nothing if index OOB
indexName :: Int -> SelectOps (Maybe SSAName)
indexName i = (!? i) <$> getLayout
  

--Note if the rhs is (x,x,x) for example, it'll emit dup*, dup1, dup1
dupToTop :: [SSAName] -> SelectOps ()
dupToTop nms = mapM_ dupName $ reverse nms
dupName :: SSAName -> SelectOps ()
dupName nm = do
  vs <- getLayout
  case elemIndex nm vs of
    Nothing -> error $ "Compiler error: dupName <missing nm> " ++ show nm
    Just i -> dupIndex i
--The EVM supports DUP1..DUP16, which duplicate index 0 to 15 respectively.
--Unlike swapIndex, this always emits an instruction.
--Does not check whether the stack is valid because dupName has already done so.
dupIndex :: Int -> SelectOps ()
dupIndex i
  | i < 0 || i > 15 = error $ "Compiler error: dup OOB " ++ show i
  | let = do
          tell [Dup (i+1)]
          vs <- getLayout
          setLayout $ (vs !! i) : vs

--The type to which a var has been bound
varType :: SSAName -> SelectOps IRT
varType nm = do
  mt <- M.lookup nm <$> gets sosVarTypes
  case mt of
    Nothing -> error $ "Compiler error: varType on missing name " ++ show nm
    Just t -> return t
setVarType :: SSAName -> IRT -> SelectOps ()
setVarType nm t = do
  m <- gets sosVarTypes
  modify (\sos -> sos{sosVarTypes = M.insert nm t m})
--Tells you whether the var has exactly one use left (implying it won't be
--needed after this op if it's part of a rhs).
isLastUse :: SSAName -> SelectOps Bool
isLastUse nm = (== 1) <$> usesRemaining nm
--Tells you whether the var has no more uses and thus can freely be popped
isGarbage :: SSAName -> SelectOps Bool
isGarbage nm = (== 0) <$> usesRemaining nm
--The number of remaining uses (ops that use + branch on + 1 if live)
usesRemaining :: SSAName -> SelectOps Int
usesRemaining nm = do
  uses <- gets sosUsesRemaining
  case M.lookup nm uses of
    Nothing -> error $ "Compiler error: usesRemaining of nonexistent var "
               ++ show nm
    Just i -> return i
decrementUses :: SSAName -> SelectOps ()
decrementUses nm = do
  i <- usesRemaining nm
  modify (\sos -> sos{sosUsesRemaining = M.insert nm (i-1) $
                       sosUsesRemaining sos})
--Pop any garbage words that are TOS
popTOS :: SelectOps ()
popTOS = do
  vs <- getLayout
  case vs of
    [] -> return ()
    v:vs -> do
      ifM (isGarbage v)
        (pop >> popTOS)
        (return ())
pop :: SelectOps ()
pop = do
  vs <- getLayout
  case vs of
    [] -> error $ "Compiler error: impossible pop emitted"
    v:vs' -> do
      tell [Opcode "pop"]
      setLayout vs'
getLayout :: SelectOps [SSAName]
getLayout = sosLayout <$> get
setLayout :: [SSAName] -> SelectOps ()
setLayout vs = modify (\sos -> sos{sosLayout=vs})

-- ****************************************************************************
--Alright, now we should have a complete map from L's to CSLCs
--Now we need to assemble them into lists of asms that fall through to each
--other.
--Simple algo: go through the CSLCs in arbitrary order, building up the lists
--as we go. I'll use an Okasaki queue for cheap append.
{-
lists = {}
While lab <- map:
 slcs <- follow lab
 lists[lab] = slcs
follow lab:
 if Just xs = lists[lab],
  delete lists[lab]
  return xs
 else:
  slc <- map[lab]
  delete lab from map
  slcs <- tryFollow slc
  return (slc:slcs)
-}
--Result: a map label -> [asm]. To serialize, simply concatenate the elements.
collectIntoLists :: Map L CSLC -> Map L [[Asm]]
collectIntoLists m = snd $ execState collectIntoListsM (m,M.empty)
collectIntoListsM :: State (Map L CSLC, Map L [[Asm]]) ()
collectIntoListsM = do
  m <- gets fst
  case M.lookupMax m of
    Nothing -> return ()
    Just (lab,_) -> do
      asms <- follow lab
      modify (id *** M.insert lab asms)
  where
    follow :: L -> State (Map L CSLC, Map L [[Asm]]) [[Asm]]
    follow lab = do
      masms <- gets (M.lookup lab . snd)
      case masms of
        Nothing -> do
          mslc <- gets (M.lookup lab . fst)
          modify (M.delete lab *** id)
          case mslc of
            Nothing -> error "This should never happen"
            Just slc -> do
              let asm = cslcOps slc
              asms <- case cslcFallthrough slc of
                        Nothing -> return []
                        Just lab' -> follow lab'
              return $ asm:asms
        Just asms -> do
          modify (id *** M.delete lab)
          return asms
collectIntoAsm :: Map L [[Asm]] -> [Asm]
collectIntoAsm l2asms = do
  (_,asms) <- M.toList l2asms
  asm <- asms
  asm
 
