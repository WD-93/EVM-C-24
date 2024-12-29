{-# LANGUAGE LambdaCase #-}
module ToyCFG where

import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.State
import Data.Maybe (fromMaybe)
import Control.Monad.Reader
import Control.Arrow ((***))

import DTs (Name(..))
import IR1

--To pretty-print CFGs in Pretty.hs I need to present them in a logical order;
--I choose DFS from the function entry point. It makes sense to put the code
--to DFS the graph here.
--Errors if there is an edge to a nonexistent node; shows only the nodes
--reachable from the entry point.
dfsGraph :: (Show k, Show v, Ord k, Ord v) =>
 (v -> [k]) -> --how to interpret nodes to get their out-edges
  k -> --the key to start from
  Map k v -> --the graph
  [(k,v)] --the reachable mappings in DFS order
dfsGraph edg k m =
  case runState (dfsGraphM edg m k) ([],S.empty) of
    (_,(vs,_set)) -> reverse vs --a poor man's writer monad
dfsGraphM :: (Show k, Show v, Ord k, Ord v) => (v -> [k]) -> Map k v -> k ->
  State ([(k,v)],Set k) ()
dfsGraphM edg m k = do
  (kvs,visited) <- get
  if S.member k visited
    then return ()
    else case M.lookup k m of
    Nothing -> error $ "Eh!? Edge to nowhere in dfsGraph: " ++
               show (k,m)
    Just v -> do
      --emit v and mark as visited
      put ((k,v):kvs,S.insert k visited)
      mapM_ (dfsGraphM edg m) (edg v)
--TODO ensure this isn't duplicated
slcChildren :: SLC nm -> [Label]
slcChildren slc = branchChildren $ slcBranch slc
branchChildren = \case
  Jump l -> [l]
  Jumpi _ th el -> [th,el]
  BReturn _ -> []
--dfsGraph specialized to CFGS
dfsCFG :: (Label,CFGS) -> [(Label,SLC Name)]
dfsCFG (lab,cfgs) | lab2slc <- labelSLCMap cfgs =
                      dfsGraph slcChildren lab lab2slc 

--For experimenting with how to simultaneously generate CFG and tag each SLC
--with live vars.
--type Name = String
annotIR :: IRP a -> a
annotIR = \case
  Op a _ _ _ -> a
  Ifte a _ _ _ -> a
  While a _ _ _ -> a
  DoWhile a _ _ _ -> a
  Return a _ -> a
  Break a _ -> a
  Continue a _ -> a
  TailCall a _ _ -> a
--The live of a given block
annotBlock :: [IRP a] -> Maybe a
annotBlock = \case
  [] -> Nothing
  ir:_ -> Just $ annotIR ir
--The name param is so I can apply SSA

type Label = Int
{-
data Branch v = BReturn [v]
            | Jump Label
            | Jumpi v Label Label
  deriving (Eq,Ord,Read,Show)
-}

type Live = Set Name
annIRWithLive :: [(Live,Live)] -> --the stack of while start and end lives
                 Live -> --the scope to fall through to if not a branch
                 IR ->
                 (IRP Live, Live)
annIRWithLive loopLs end =
  let rs = annIRsWithLive loopLs end in
    \case
      Op () lhs op rhs ->
        let end' = applyOp end lhs rhs
        in (Op end' lhs op rhs, end')
      Ifte () v th el ->
        let (th',end1) = rs th
            (el',end2) = rs el
            s = S.insert v $ end1 `S.union` end2
        in (Ifte s v th' el',s)
      --This is the tricky one: we update loopLs, do one pass with the
      --assumption continue has live {}, then fill in with the proper value.
      --We assume only two passes are needed.
      --We do not assume v must be defined by pre.
      --while pre v post =>
      --loop:
      --pre
      --if v {post; goto loop} {}
      --Note this adds explicit continues to the end of every loop body
      While () pre v post ->
        let initialLoop = S.empty
            post' = post ++ [Continue () 0]
            (_,end') = annIRWithLive ((initialLoop,end):loopLs) end
              (Ifte () v post' [])
            --This is the final loop label
            (_,loop) = annIRsWithLive loopLs end' pre
            --While body:
            (Ifte loopCont _ loopBody [], _) =
              annIRWithLive ((loop,end):loopLs) end (Ifte () v post' [])
            (pre',loop') = annIRsWithLive loopLs loopCont pre
            --Defensive programming... if this blows up I was wrong and need
            --to iterate to fixpoint.
        in if loop' /= loop
           then error "Looks like I was wrong!"
           else (While loop pre' v loopBody, loop)
      --Note end is discarded in branching instructions!
      Return () vs ->
        let s = S.fromList vs
        in (Return s vs, s)
      Break () ix ->
        case loopLs !? ix of
          Just (start,end) -> (Break end ix,end)
          Nothing -> error $ "Break index out of bounds: " ++ show (ix,loopLs)
      Continue () ix ->
        case loopLs !? ix of
          Just (start,end) -> (Continue start ix, start)
          Nothing -> error $ "Continue index OOB: " ++ show (ix,loopLs)

(x:xs) !? 0 = Just x
(x:xs) !? n | n > 0 = xs !? (n - 1)
_ !? _ = Nothing
--It's a foldr so we're accumulating from the back
annIRsWithLive loopLs end irs =
  go end irs
  where
    go end = \case
      [] -> ([],end)
      ir:irs ->
        let (irs',end') = go end irs
            (ir',end'') = annIRWithLive loopLs end' ir
        in (ir':irs',end'')
applyOp end lhs rhs = S.union (S.fromList rhs) $
  end S.\\ S.fromList (map fst lhs)
  {-\case
  [] -> end
  (lhs,rhs):ops ->
    S.union (S.fromList rhs) $ applyOps end ops  S.\\ S.fromList lhs
-}

annFun = annIRsWithLive [] S.empty
--Each block generates a new graph, potentially connected to the old.
--Params: live set, end branch.
--Why pass in a branch? Because if, while and return terminate the SLC
--above it.

--Some test AST combinators
x =: ws = Op () [(x,tword)] (Opcode "meh") $ words ws
ret ws = Return () $ words ws
while x = While () x
ifte x = Ifte () x
cont = Continue ()
brk = Break ()

--while cond {y = x; x = 1}; return y
testLoop =
  [while [] "x" [
      "y" =: "x",
      "x" =: ""
      ],
    ret "y"
  ]
testNested =
  [while ["x" =: "y"] "x" [
      "z" =: "y",
      ifte "z" [
          brk 0
      ] [],
      while [] "y" [
          cont 1
          ],
      ret "x y z a"
      ],
    ret "w"
  ]

data SLC v = SLC {slcOps :: [([(v,IRT)],Operator,[v])],
                  slcBranch :: Branch v,
                  slcLive :: Live
                 }
  deriving (Eq,Ord,Read,Show)
data Branch v = Jump Label
              | Jumpi v Label Label
              | BReturn [v]
  deriving (Eq,Ord,Read,Show)

type CFGM = State CFGS
data CFGS = CFGS {labelCtr :: Label,
                  labelSLCMap :: Map Label (SLC Name)
                 }
  deriving (Eq,Ord,Read,Show)
type LL = (Label,Live)
runCFG :: CFGM a -> (a,CFGS)
runCFG cfgm = runState cfgm $ CFGS 0 M.empty

cfgFun :: [IRP Live] -> CFGM (Maybe LL)
cfgFun = cfg [] Nothing

--The main, useful function
ir2cfg :: [IR] -> (Maybe LL, CFGS)
ir2cfg = runCFG . cfgFun . fst . annFun
--The end label of while loops is a Maybe LL because it's a continuation.
--That solves the edge case where the while loop has no cont, but it's fine
--because the loop cond always returns.
--If either branch of an ifte returns a Nothing, generate no node and return
--a Nothing. To be well-formed, the function must return a Just.
cfg :: [(LL,Maybe LL)] -> Maybe LL -> [IRP Live] -> CFGM (Maybe LL)
cfg loopLs mll = \case
  [] -> return mll
  Return live vs : _ -> do
    genSLC live [] (BReturn vs)
  Break a n : _
    | Just (start,end) <- loopLs !? n ->
      return end
  Continue a n : _
    | Just (start,end) <- loopLs !? n ->
      return (Just start)
  Op live lhs op rhs : irs -> do
    mll' <- cfg loopLs mll irs
    case mll' of
      Nothing -> return Nothing
      Just (cont,_) -> do
        genSLC live [(lhs,op,rhs)] (Jump cont)
  Ifte live v th el : irs -> do
    end <- cfg loopLs mll irs
    mth <- cfg loopLs end th
    mel <- cfg loopLs end el
    genIfte live v mth mel
  --loop: pre, jump condCheck
  --condCheck: jumpi v loopBody end
  --loopBody: post (continue is included)
  --the body generation will always succeed, though it may point to a
  --nonexistent loop. That's not a problem, since if loop doesn't exist then
  --the body won't be reachable.
  While liveLoop pre v post : irs -> do
    end <- cfg loopLs mll irs
    loop <- newLabel
    let loopll = (loop,liveLoop)
    mbody <- cfg ((loopll,end):loopLs) (Just loopll) post
    case mbody of
      Just (body,liveBody) -> do
        let liveCheck = S.insert v $ S.union liveBody liveLoop
        condCheck <- genIfte liveCheck v (Just (body,liveBody)) end
        trueLoop <- cfg loopLs condCheck pre
        case trueLoop of
          Nothing -> return Nothing
          Just (trueLoopLabel,_) -> do
            --redirect loop to trueLoop
            createSLC loop SLC{slcOps = [],
                               slcBranch = Jump trueLoopLabel,
                               slcLive = liveLoop
                              }
            return $ Just (loop,liveLoop)
      Nothing -> error "This won't happen!"

genIfte :: Live -> Name -> Maybe LL -> Maybe LL -> CFGM (Maybe LL)
genIfte live v mth mel =
  case (mth,mel) of
    (Just (t,_), Just (e,_)) -> do
      l <- newLabel
      genSLC live [] (Jumpi v t e)
    _ -> return Nothing
genSLC :: Live -> [([(Name,IRT)],Operator,[Name])] -> Branch Name ->
  CFGM (Maybe LL)
genSLC live ops branch = do
  l <- newLabel
  createSLC l SLC{slcOps = ops,
                  slcBranch = branch,
                  slcLive = live
                 }
  return $ Just (l,live)

newLabel :: CFGM Label
newLabel = do
  s <- get
  let lab = labelCtr s
  put s{labelCtr = lab + 1}
  return lab
createSLC :: Label -> SLC Name -> CFGM ()
createSLC l slc = do
  s <- get
  case M.lookup l $ labelSLCMap s of
    Nothing -> put s{labelSLCMap = M.insert l slc $ labelSLCMap s}
    Just slc' -> error $ "Label collision: " ++ show (l,slc,slc')

--First valid version: 0. That means you can just add vcount maps together,
--regardless of whether a var is live or not. If v0 is mentioned in a SLC,
--v must be live.
type SSAName = (Int,Name)
--For vars = op args in ops,
-- replace each arg with ssaNm[arg]
-- increment version of each var and then replace
--For each var in branch, replace it with ssaNm[var]
--Elim copies separately
--The resulting SLC will have the meaning of its ops be order-independent,
--but they'll be ordered st any (ver,x) in LHS precludes future use of
--(ver-1,x)... until I elim copies. Future opts will need to take that into
--account.
--Why also save the version counter map? Because if you jump to an empty SLC
--with branch jumpi v _ _ or return (v:_), you need to substitute those vs
--correctly to merge them. That entails incrementing their versions and summing
--the version count maps.
ssaSLC :: SLC Name -> (SLC SSAName, Map Name Int)
ssaSLC slc = runState
  (do let ops = slcOps slc
          b = slcBranch slc
          live = slcLive slc
      ops' <- mapM ssaOp ops
      b' <- ssaBranch b
      return $ SLC {slcOps = ops',
                    slcBranch = b',
                    slcLive = live
                   })
  M.empty
type SSA = State (Map Name Int)
type SSAOp = ([(SSAName,IRT)],Operator,[SSAName])
--TODO opt: eliminate double seek in map per nm increment+lookup
ssaOp :: ([(Name,IRT)],Operator,[Name]) ->
         SSA SSAOp
ssaOp (nmts,op,args) = do
  ssargs <- mapM ssaNm args
  ssanmts <- mapM (\(nm,t) -> do
                      --The ordering of incVer and ssaNm is vital here;
                      --on first assignment to x (e.g. x = copy y), x's
                      --version is 1. That prevents confusion in mergeSLCs.
                      incVer nm
                      ssanm <- ssaNm nm
                      return (ssanm,t)
                  ) nmts
  return (ssanmts,op,ssargs)
ssaBranch :: Branch Name -> SSA (Branch SSAName)
ssaBranch = \case
  Jumpi v th el -> Jumpi <$> ssaNm v <*> return th <*> return el
  BReturn vs -> BReturn <$> mapM ssaNm vs
  Jump l -> return $ Jump l
ssaNm :: Name -> SSA SSAName
ssaNm nm = do
  v <- getVer nm
  return (v,nm)
getVer :: Name -> SSA Int
getVer nm = nameVer nm <$> get 
--Also used in SLC merge, dead op pruning
nameVer :: Name -> Map Name Int -> Int
nameVer v = fromMaybe 0 . M.lookup v
--Increment name version count; done on assignment
incVer :: Name -> SSA ()
incVer nm = do
  v <- getVer nm
  s <- get
  put $ M.insert nm (v+1) s

--Doesn't need to modify the version count map; the same map guarantees
--uniqueness even if you elim vars.
--For each xN = copy yM in ops, substitute subsequent xN's for yM and elim
--the copy op.
--When x(N+1) is encountered in a LHS, xN is out of scope and you can delete
--it from the subst map... but you don't have to.
--Finally, subst in the branch.
--To merge SLCs, need to remember this subst map too.
--First apply the SSA subst, then this one.
elimCopiesSLC :: SLC SSAName -> (SLC SSAName,Map SSAName SSAName)
elimCopiesSLC slc = runState
  (do let ops = slcOps slc
          b = slcBranch slc
      ops' <- ecOps ops
      b' <- ecB b
      return $ slc{slcOps=ops',slcBranch=b'}
  )
  M.empty
--Elim copy monad
type ECp = State (Map SSAName SSAName)
ecNm :: SSAName -> ECp SSAName
ecNm nm = nameSubst nm <$> get
--Also used in SLC merge
nameSubst :: SSAName -> Map SSAName SSAName -> SSAName
nameSubst nm = fromMaybe nm . M.lookup nm
ecB :: Branch SSAName -> ECp (Branch SSAName)
ecB = \case
  Jumpi v th el -> Jumpi <$> ecNm v <*> return th <*> return el
  BReturn vs -> BReturn <$> mapM ecNm vs
  Jump l -> return $ Jump l
ecOp :: SSAOp -> ECp [SSAOp]
ecOp = \case
  --The t need not be the same as y's t, but as long as I haven't made a
  --kind error earlier forgetting _t shouldn't be a problem.
  ([(x,_t)],Copy,[y]) -> do
    y' <- ecNm y
    ecAddSubst x y'
    return [] --the op will be deleted
  --Single-argument reduce is just a copy, because reduce is only valid for
  --commassoc ops with an identity.
  --That copy should be eliminated here.
  (lhs,Reduce op,[x]) -> ecOp (lhs,Copy,[x])
  --Might as well elim reduce op [] here
  (lhs,Reduce op,[]) ->
    return [(lhs,Push $ Const $ reduceOpIdentity op,[])]
  (lhs,op,rhs) -> do
    rhs' <- mapM ecNm rhs
    --We could prune the subst map here, but that's an O(n log m) operation
    --to reduce the size of an O(log m) structure, so we don't do it.
    return [(lhs,op,rhs')]
--TODO move this somewhere sensible
reduceOpIdentity :: Name -> Integer
reduceOpIdentity = \case
  "or" -> 0
  "add" -> 0
  "mul" -> 1
  "smul" -> 1
  op -> error $ "Compiler error: op with unknown identity: " ++ show op
    
ecOps :: [SSAOp] -> ECp [SSAOp]
ecOps ops = concat <$> mapM ecOp ops
--To avoid having to follow a chain of substitutions later, we need to
--maintain the invariant that each x maps to its ultimate copy source.
--Thankfully, substituting the rhs in (lhs,op,rhs) in ecOp gives us that for
--free.
ecAddSubst :: SSAName -> SSAName -> ECp ()
ecAddSubst x y = modify (M.insert x y)

--A function's pre-SSA CFG -> SSA, elim copies,
--add version count and copy subst maps, add in-edges count
type SLC2 = (SLC SSAName, --the SLC itself
             Map Name Int, --version count map
             Map SSAName SSAName, --copy subst map
             Int --in-edges count
            )
type CFG2 = Map Label SLC2
--No need to look at the live set of the function entry point here
--Starting from the entry point, SSA + copy-elim the pointed SLC
--,recurse on the ones branched to and increment their in-edges.
--Use the accumulated map to limit DFS traversal.
--TODO find a better name than process.
--On a branch to a nonexistent SLC, throw an exception; that shouldn't happen
--here, so it's a compiler error.
--No need to incInEdges first, procLabel start will insert an SLC2 for start
--with in-edges = 1
processCFG :: (Label,Map Label (SLC Name)) ->
          (Label,CFG2)
processCFG (start,l2slc) =
  (start,execState (runReaderT (procLabel start) l2slc)
         M.empty)

type Proc = ReaderT (Map Label (SLC Name)) (State CFG2)
procLabel :: Label -> Proc ()
procLabel lab = do
  b <- M.member lab <$> get
  if b
    then incInEdges lab
    else do
    mslc <- M.lookup lab <$> ask
    case mslc of
      Nothing ->
        error $ "Compiler error: label to nowhere in procLabel: " ++ show lab
      Just slc -> do
        let (slc1,verMap) = ssaSLC slc
            (slc2,substMap) = elimCopiesSLC slc1
        modify (M.insert lab (slc2,verMap,substMap,1))
        --Recurse on reached SLCs
        mapM_ procLabel $ slcChildren slc
incInEdges :: Label -> Proc ()
incInEdges lab = do
  s <- get
  case M.lookup lab s of
    --Would having a separate label -> in-edges map reduce pointless
    --reallocation? Probably not... but no matter, it's a minor perf issue.
    Just (slc,vm,sm,n) -> modify $ M.insert lab (slc,vm,sm,n+1)
    Nothing -> error $ "Compiler error: incInEdges <label to nowhere>: " ++
      show lab

--Now:
--Deterministic jumpi => jump (may shrink live, but we don't detect that now)
--How to detect later? Live slc = v0s | (live children \ set in slc)
--Note that doesn't prune vars live in cycles.

--The algo for traversing the CFG2
--When a ->1 b is found, merge them and delete b.
--Detect jumpis to two equivalent SLCs and replace with a jump?
--That could be generalized to subgraph isomorphism, but let's not for now.
--Order of operations: merge first if possible (it's equivalent to bypass
--when it applies), then maybe bypass children (potentially leaving a node
--containing only substs). If the branch is a jumpi and both now point to the
--same label, replace with a jump.
--An empty SLC with no substs can always be eliminated.
--Should the refcount of the start node be >= 1? Yes, consider if the
--function body is simply a while; the continue should not be a unique edge.
--Each opt updates the current SLC, potentially modifying the refcount of other
--nodes.
--If any update was done in a pass, do a DFS GC and continue.
--That should future-proof against DCE.
--An additional potential opt: deletion of irrelevant ops.
--Ex: if(cond){x = 1} {x = 2}
--If x is dead afterward, that becomes just cond.
--Recursively modify, tracking the DFS path. A back-edge should not be
--bypassed. No need to keep track of order; the continuation after the
--recursive call will do that.
--Type: Label -> m Label?
--To bypass I need to merge because the empty SLC may contain substs...
--It's cheaper to left-accumulate when merging, so perhaps find the chain of
--one-edges before merging.

--For now, I'll just do the 1-edge merge and jumpi=>jump, not bypass.
--Monad for optimizing CFG2
--Full GC and jumpi=>jump may enable new merges, so repeatedly do a DFS opt
--pass and GC until you reach a fixpoint. Each iteration should simplify the
--CFG, so it shouldn't loop forever.
--In future, the entrypoint label may change due to the first node being
--bypassable.
opt2 :: Label -> CFG2 -> CFG2
opt2 lab cfg =
  let cfg' = dfsGC lab $ opt2Pass lab cfg
  in if cfg == cfg'
     then cfg
     else opt2 lab cfg'
--Returns a graph containing only the nodes reachable from label
--To adjust in-edges, it must also delete the garbage.
--When iterating over the garbage labels, some may already have been deleted,
--so you need to check that before running deleteSLC2 (which assumes
--presence).
--I could fuse the two passes into one if I incremented the refcounts from 1
--again.
dfsGC :: Label -> CFG2 -> CFG2
dfsGC lab cfg2 =
  execState (do let reachableNodes =
                      S.fromList $ map fst $ dfsGraph slc2Children lab cfg2
                    garbageNodes =
                      filter (not . flip S.member reachableNodes) $
                      M.keys cfg2
                mapM_ (\garbage -> do
                          b <- gets (M.member garbage)
                          if b
                            then deleteSLC2 garbage
                            else return ())
                  garbageNodes)
  cfg2
opt2Pass :: Label -> CFG2 -> CFG2
opt2Pass lab cfg = snd $ execState (opt2PassM lab) (S.empty,cfg)
--The set of already visited nodes and the CFG being optimized
type Opt2 = State (Set Label, CFG2)
--If already visited, just return the current SLC2
--Otherwise, recurse on the children.
--If the current SLC is a deterministic jumpi, convert it to a jump.
--If it just has a 1-edge to a single child, merge them.
opt2PassM :: Label -> Opt2 SLC2
opt2PassM lab = do
  slc2 <- opt2GetSLC2 lab
  b <- opt2Visited lab
  if b
    then return slc2
    else do
    opt2MarkVisited lab
    slcs <- mapM opt2PassM $ slc2Children slc2
    --Prune dead ops... this one's probably expensive, so I should figure out
    --how to cache it.
    let contLive = S.unions $ map (slcLive . slc2ToSLC) slcs
        (_,vmap,smap,_) = slc2
        --Version and substitute.
        --Note the version count in the vmap is the index of the last var
        --assigned, not of the next one to be assigned.
        contLiveVS = S.map ((\v ->
                               case M.lookup v smap of
                                 Just v' -> v'
                                 Nothing -> v) .
                             (\nm -> (nameVer nm vmap, nm))) contLive
        oldSLC2 = slc2
    let slc2 = pruneDeadOpsSLC2 oldSLC2 contLiveVS
    --Debugging...
    let isTargetOps [([((1,"$anon1"),_)],_,_),
                     ([((1,"$anon2"),_)],_,_)] = True
        isTargetOps _ = False
    if isTargetOps $ slcOps $ slc2ToSLC oldSLC2
      then error $ "Found it:" ++ show (oldSLC2,slc2,oldSLC2 == slc2)
      else return ()
    --If the current SLC is a deterministic jump...
    let (slc,v,s,rc) = slc2
    case slcBranch slc of
      Jumpi _ th el
        | th == el ->
            opt2UpdateSLC lab slc2 (slc{slcBranch = Jump th},
                                    v,s,rc)
      Jump cont
        | [slc2Cont] <- slcs,
          (_,_,_,1) <- slc2Cont ->
          opt2UpdateSLC lab slc2 $ mergeSLCs slc2 slc2Cont
      --Bypassing for jump to empty is ez
      --Backjumps are fine?
      --I don't see any difference in generated CFGs...
      --Perhaps the LL passing in ir2cfg is already handling it.
      --No matter, irrelevant op elimination and other opts will make use of it
        | [slc2Cont] <- slcs,
          [] <- slcOps $ slc2ToSLC slc2Cont ->
          opt2UpdateSLC lab slc2 $ mergeSLCs slc2 slc2Cont
      _ -> return slc2
opt2UpdateSLC :: Label -> SLC2 -> SLC2 -> Opt2 SLC2
opt2UpdateSLC lab old new = do
  modify (id *** updateSLC2 lab old new)
  return new
opt2GetSLC2 :: Label -> Opt2 SLC2
opt2GetSLC2 lab = do
  cfg <- gets snd
  case M.lookup lab cfg of
    Nothing -> error $ "Compiler error: LTN in getSLC2 " ++ show lab
    Just slc2 -> return slc2
opt2Visited :: Label -> Opt2 Bool
opt2Visited lab = gets (S.member lab . fst)
opt2MarkVisited :: Label -> Opt2 ()
opt2MarkVisited lab = modify (S.insert lab *** id)

slc2ToSLC :: SLC2 -> SLC SSAName
slc2ToSLC (slc,_,_,_) = slc
slc2Children :: SLC2 -> [Label]
slc2Children = slcChildren . slc2ToSLC

--Given an SLC and the live set of all branches, delete all ops which generate
--no vars relevant to the branch. Note ops which return multiple vars may
--have a subset of them be relevant; then you're left with dead vars but the
--op is not pruned.
--Note that the live set at the last op is not always the live set of the
--potential dests, since jumpi may depend on a var. In future, other branches
--may also do the same.
--prune may also shrink live.
--Algo: proceed from last op, with needed = live
--For each op, if none of its lhs vars are used, delete it.
--Otherwise, add its rhs vars to needed.
--TODO make a helper that gets vars from branch.
--That the version count map is polluted with dead vars is not a problem... but
--what if a substituted var belongs to a dead op? We'll see... it's unlikely
--to cause any bugs for now; just remember vars in the subst map need not
--correspond to a live op.
--Note that thanks to SSA there's no need to consider shadowing.
pruneDeadOpsSLC2 :: SLC2 -> SSALive -> SLC2
pruneDeadOpsSLC2 (slc,v,s,rc) live =
  let branchLive =
        case slcBranch slc of
          Jumpi v _ _ -> S.singleton v
          BReturn vs -> S.fromList vs
          Jump _ -> S.empty
      live' = live `S.union` branchLive
  in (slc{slcOps = pruneDeadOps (slcOps slc) live'},v,s,rc)
--TODO use elsewhere
type SLCOp v = ([(v, IRT)], Operator, [v])
type SSALive = Set SSAName
--Returns a filtered op list
pruneDeadOps :: [SSAOp] -> SSALive -> [SSAOp]
pruneDeadOps ops live =
  fst $ foldr handleOp ([],live) ops
  where
    handleOp (lhs,op,rhs) (ops,live) =
      let results = map fst lhs in
        if all (not . flip S.member live) results
        then (ops,live)
        else ((lhs,op,rhs):ops,live `S.union` S.fromList rhs)

--Convert a deterministic jumpi to a jump. Nothing indicates no change.
detJumpiToJump :: SLC2 -> Maybe SLC2
detJumpiToJump (slc,v,s,r)
  | Jumpi _ th el <- slcBranch slc,
    th == el = Just (slc{slcBranch = Jump th},v,s,r)
  | let = Nothing

--The refcount map for the children of an SLC; written so I can add new
--branch types later (such as case or dispatch) without modifying this.
slc2ChildMap :: SLC2 -> Map Label Int
slc2ChildMap (slc,_,_,_) = slcChildMap slc
slcChildMap :: SLC v -> Map Label Int
slcChildMap = M.fromListWith (+) . map (\k -> (k,1)) . slcChildren
--Given two refcount maps, get the diff in refcount per child (due to updating
--an SLC).
childMapDiff :: Map Label Int -> Map Label Int -> Map Label Int
childMapDiff m1 = M.unionWith (+) m1 . M.map negate
--Update an SLC2 from the old to the new value
--Precondition: the old value matches that found in the map.
updateSLC2 :: Label -> SLC2 -> SLC2 -> Map Label SLC2 -> Map Label SLC2
updateSLC2 lab old new m =
  let cm1 = slc2ChildMap old
      cm2 = slc2ChildMap new
      --d[l] > 0 if new edges are added; < 0 if they're deleted on net
      d = childMapDiff cm2 cm1
  in applyChildMapDiff d $ M.insert lab new m
  --Note the order: recursive edge decrements must be done to the new SLC, not
  --the old one.

--Note mappings may include 0
--Apply the edge increments first, so recursive decrements due to deletions
--don't wrongly delete a node.
--Ex: A(1) -> B(1), A--, B++.
applyChildMapDiff :: Map Label Int -> Map Label SLC2 -> Map Label SLC2
applyChildMapDiff l2n m =
  let incs = M.toList $ M.filter (>0) l2n
      decs = M.toList $ M.filter (<0) l2n
  in execState (mapM applyInc incs >> mapM applyDec decs) m
--Introduced to chase a weird type error...
--Fixed: turns out I was shadowing the (s)tate with the (s)ubst map
getSLC2 :: String -> Label -> State (Map Label SLC2) SLC2
getSLC2 loc l = do
  mslc2 <- gets (M.lookup l)
  case mslc2 of
    Nothing -> error $ "Compiler error: label to nowhere in " ++ loc ++ " "
               ++ show l
    Just slc2 -> return slc2
--Precondition: n > 0
applyInc :: (Label,Int) -> State (Map Label SLC2) ()
applyInc (l,n) = do
  (slc,v,s,m) <- getSLC2 "applyInc" l
  modify $ M.insert l (slc,v,s,m+n)
--Precondition: n < 0
--This may recursively delete nodes (but it doesn't catch every garbage node
--due to cycles).
applyDec :: (Label,Int) -> State (Map Label SLC2) ()
applyDec (l,n) = do
  (slc,v,s,m) <- getSLC2 "applyDec" l
  case () of
    _ | m + n < 0 -> error $ "Compiler error: negative refcount in applyDec!? "
                     ++ show (l,n)
      | m + n == 0 -> deleteSLC2 l
      | let -> modify $ M.insert l (slc,v,s,m+n)
--Note that none of the recursively deleted nodes will have a back-edge to the
--current node, since then it wouldn't have had a refcount of 0.
--That means we can safely delete it before recursing.
deleteSLC2 :: Label -> State (Map Label SLC2) ()
deleteSLC2 l = do
  slc2 <- getSLC2 "deleteSLC2" l
  modify (M.delete l)
  let decs = M.toList $ childMapDiff M.empty $ slc2ChildMap slc2
  mapM_ applyDec decs

--SLC merge; a can be merged with b if a jumps to b and b has a refcount of 1.
--The merged SLC has a's ops, followed by b's renamed ops and b's renamed
--branch; it retains a's refcount.
--Now that the first valid version is 0, v[n] in slcB => v[n+vA[v]]
--Apply the SSA renaming, then the subst map (which can only apply to xn's).
--The version count map is simply summed.
--The subst map sB first has its keys and values renamed. If sB[x] = y, y may
--in turn be substitued by sA; apply that subst to preserve the invariant that
--you can find the ultimate copied var in 1 lookup. 
mergeSLCs :: SLC2 -> SLC2 -> SLC2
mergeSLCs (slcA,vA,sA,rcA) (slcB,vB,sB,_) =
  let opsM = slcOps slcA ++ map (renameOp vA sA) (slcOps slcB)
      f = renameVar vA sA
      branchM =
        case slcBranch slcB of
          Jump l -> Jump l
          Jumpi v th el -> Jumpi (f v) th el
          BReturn vs -> BReturn $ map f vs
      liveM = slcLive slcA
      vM = M.unionWith (+) vA vB
      --First rename both keys and values; note that while multiple x0, y0
      --in slcB may be mapped to the same name from slcA, any key in sB will
      --have version >= 1 and so f (renameVar) will be injective.
      --Since f also applies sA, the ultimate copied var can still be found in
      --1 lookup.
      --Finally, combine with sA. Note the keys of sA and the renamed sB are
      --disjoint.
      sM = M.union sA $ M.map f (M.mapKeys f sB)
  in (SLC{slcOps = opsM,
          slcBranch = branchM,
          slcLive = liveM
         },
       vM,sM,rcA)
renameOp :: Map Name Int -> Map SSAName SSAName ->
            ([(SSAName,IRT)],Operator,[SSAName]) ->
            ([(SSAName,IRT)],Operator,[SSAName])
renameOp vA sA (lhs,op,rhs) =
  let f = renameVar vA sA in
    (map (f *** id) lhs, op, map f rhs)
--There's no need to look at sB, since sB's substs have already been applied
--and any var is substituted by sB just has its version count bumped.
renameVar :: Map Name Int -> Map SSAName SSAName -> SSAName -> SSAName
renameVar vA sA (n,v) = nameSubst (n + nameVer v vA, v) sA
--SLC bypass
--Divergence detection? There is no detectable divergence, so no.
--Each opt restricts the forms the other opts need to consider.
--SLC merge: you're left with only jumpi, return, and jumps to shared nodes.

--SLC merge: subst maps map each x to its ultimate copy source. That
--invariant needs to be maintained in the merged SLC.
                        
--Now what?
--1) Elim unreachable nodes
--2) Elim empty intermediate nodes
--3) Fuse SLCs which jump
--SSA, add version count to name.
--Elim copies
--Any var not set in a loop has a finite-size description? If you allow
--ifte...
--When two vars have the same description, they can be merged (though in the
--case of small constants that need not be efficient).

--Stack-aware stage:
--Select word order; that requires emitting ops
--Always consume on last use
--Insert intermediate nodes for stack shuffling
--Convert best jumpi else or jump to a fallthrough per SLC.
    
{-
--Testing a simpler, multi-stage CFG construction method: compile to sequential
--instructions a la Ecomp, then construct a CFG from that.
--IR name: pseudoassembly
type PAM = State PAS
data PAS = PAS {labelCtr :: Label,
                pasInstrs :: [PA Name]
               }
  deriving (Eq,Ord,Read,Show)
runPAM :: PAM () -> (Label,[PA Name])
runPAM pam = let PAS ctr instrs = execState pam (PAS 0 [])
             in (ctr,reverse instrs)
data PA v = PAOp [([v],[v])]
          | Jump Label
          | Jumpi v Label Label
          | PAReturn [v]
          | PlaceLabel Int
          | DeclareLive Live
  deriving (Eq,Ord,Read,Show)

type LL = (Live,Label)

ir2PA :: [IR () Name] -> [PA Name]
ir2PA irs = snd $ runPAM $ pasmFun $ fst $ annFun irs
--Problem: not all args of a function are necessarily live.
--However, it's also the case that the two dests of Jumpi have different
--live sets.
--The solution to both could be inserting stack shuffling code between nodes;
--ideally you can avoid it by merging SLCs when there's a single node.
--What should the live set of the entry point be? The live set given the
--function body, not the args (which would break the relation between live and
--future code). The actual stack layout may include garbage; if you jump back
--to a node expecting garbage, you can just put arbitrary values there.
pasmFun irs = do
  l <- newLabel
  placeLabel l --the function entry point
  pasm [] irs

--With declareLive separate from PlaceLabel, knowing the live set of the
--successor is no longer if or while's problem.
pasm :: [(Label,Label)] -> [IR Live Name] -> PAM ()
pasm loopLs = mapM_ $ pasmIR loopLs
pasmIR :: [(Label,Label)] -> IR Live Name -> PAM ()
pasmIR loopLs ir = do
  declareLive $ annotIR ir
  case ir of
    Ops _ ops -> emitPA $ PAOp ops
    If _ v th el -> do
      t <- newLabel
      e <- newLabel
      end <- newLabel
      jumpi v t e
      placeLabel t
      pasm loopLs th
      placeLabel e
      pasm loopLs el
      jump end
      placeLabel end
    While _ pre v post -> do
      loop <- newLabel
      body <- newLabel
      end <- newLabel
      placeLabel loop
      pasm loopLs pre
      jumpi v body end
      placeLabel body
      pasm ((loop,end):loopLs) post
      --jump loop
      --the jump loop is implicit because annFun adds a continue
      placeLabel end
    Return _ vs -> emitPA $ PAReturn vs
    Break _ n | Just (_,end) <- loopLs !? n -> jump end
              | let -> error "Break OOB"
    Continue _ n | Just (start,_) <- loopLs !? n -> jump start
                 | let -> error "Continue OOB"
jump = emitPA . Jump
jumpi v t e = emitPA (Jumpi v t e)
placeLabel = emitPA . PlaceLabel
declareLive = emitPA . DeclareLive
      
newLabel :: PAM Label
newLabel = do
  s <- get
  let l = labelCtr s
  put s{labelCtr = l + 1}
  return l
emitPA :: PA Name -> PAM ()
emitPA pa = do
  s <- get
  put s{pasInstrs = pa : pasInstrs s}

data SLC v = SLC {
  slcOps :: [([v],[v])],
  slcBranch :: PA v, --invariant: a branching instruction
  slcLive :: Set Name --This should in fact be name and not v
               }
  deriving (Eq,Ord,Read,Show)
-}
--Algo: declareLive and placeLabel may occur in either order
--Conflicting declareLives without an intervening op is an error.
--All SLCs must end with a branch; if we're in an SLC and encounter [], error.
--mlive: maybe we know the live (should not be changed by a non-op)
--mlabel: maybe we know the label
--Dead code can occur due to eg while(cond){continue;...}: drop it until the
--next declareLive+placeLabel
--Step 1: partition into label,live,ops,branch
{-
Patterns:
live, ops
live, jumpi v t e
placeLabel branch: ..., jump
live, placeLabel loop: ..., jumpi
placeLabel body: ..., live, jump
live, return

Empty blocks will contain only a jump and no live info.
An op can precede a placeLabel; if so add a jump
-}
--partitionPA :: [PA Name] -> [(Label,Live,[([Name],[Name])],Branch Name)]
--partitionPA = undefined
{-
--Now to build a CFG...
type CFGM = State CFGS
data CFGS = CFGS {labelCtr :: Label,
                  --No partial SLC state, only whole SLCs are placed
                  labelSLCMap :: Map Label (SLC Name)
                 }
  deriving (Eq,Ord,Read,Show)
type LL = (Label,Live) --Live is needed to create intermediate jumps
cfg :: [(LL,LL)] -> --the loop start and end labels
       LL -> --the end continuation
       [IR Live Name] -> --the block to compile
       CFGM LL --the label to jump to and its live set
cfg loopLs endlive = \case
  [] -> do let (end,live) = endlive
           emitSLC [] (Jump end) live
  Return live vs:_ -> do
    emitSLC [] (BReturn vs) live
  Break live n:_
    | Just (_,(end,_)) <- loopLs !? n ->
      emitSLC [] (Jump end) live
  Continue live n:_
    | Just ((start,_),_) <- loopLs !? n ->
        emitSLC [] (Jump start) live
  ir:irs -> do
    p@(end',live') <- cfg loopLs endlive irs
    case ir of
      Ops live ops -> emitSLC ops (Jump end') live
      If live v th el -> do
        (t,_) <- cfg loopLs p th
        (e,_) <- cfg loopLs p el
      emitSLC [] (Jumpi v t e) live
      --Note post is nonempty
      --pre -> check
      --check = jumpi v body end'
      --body -> pre
      --Can't use emitSLC...
      --I need check and body's live... store them in While?
      --checkLive = live' | bodyLive | v
      While live pre v post -> do
        loop <- newLabel
        check <- newLabel
        body <- newLabel
        --Instead of setting pre's start label, we generate an intermediate
        --node that jumps to it.
        
emitSLC ops b live = do
  l <- newLabel
  emitSLCLabel l ops b live
emitSLCLabel :: Label -> [([Name],[Name])] -> Branch Name -> Live -> CFGM LL
emitSLCLabel l ops b live = do
  s <- get
  let m = labelSLCMap s
  put s{labelSLCMap = M.insert l SLC{slcOps = ops,
                                      slcBranch = b,
                                      slcLive = live
                                    } m
       }
  return (l,live)
--Return the root label of the generated SLCs?
--Because I support break and continue out of nested loops, I need a loopLs
--stack param as well.
--end is the default continuation, e.g. the statement after an ifte in
--if(cond){return 0} else {x = 3}
--The else branch will jump to end, the then will not.
{-
cfg :: [(Label,Label)] -> Branch Name -> [IR Live Name] -> CFGM ()
cfg loopLs end = \case
  [] -> branch end
  --branching instructions; may not be followed by any other instrs in the
  --same block
  [Return _ vs] -> branch $ BReturn vs
  [Break _ n]
    | Just (start,end) <- loopLs !? n ->
      branch (Jump end)
    | let -> error "Break OOB"
  [Continue _ n]
    | Just (start,end) <- loopLs !? n ->
      branch (Jump end)
    | let -> error "Continue OOB"
  ir:irs ->
    case ir of
      --Live doesn't matter, we already know the current SLC live
      Ops _ ops -> appendOps ops
      --The information I need in if is the live of its branches, not of if
      --itself... however, ifLive must be retained to get the live info for
      --nested ifs.
      --if(v){}{} can be eliminated, allowing subsequent ops to continue to
      --be accumulated into one SLC
      --Note if one branch is empty, its live may be a subset of if's live and
      --thus you should allocate a new SLC for it.
      --When live if == live cont, there's no need.
      --Special case: irs = []. Then continue to end
      If _ _ [] [] -> cfg loopLs end irs
      If _ v th el -> do
        (c,bc) <- dBlock end irs
        (t,bt) <- dBlock c th
        (e,be) <- dBlock c el
        branch (Jumpi v t e)
        cBlock bt
        cBlock be
        cBlock bc
      --Special cases: pre empty (does that ever happen?), post empty
      --dBlock/cBlock handles that.
      --Emitting empty SLCs handles the problem of whether dBlock needs a
      --branch argument; they can be pruned later.
      --Note the body is never empty: it always contains a continue!
      While liveLoop pre v post -> do
        endLoop <- newLabel
        loop <- newLabel
        body <- newLabel
        --pre must end with a jumpi... but what if pre is empty?
        --Always place a new SLC for it and jump to it at the end of the loop.
        setLabel loop liveLoop
        cfg loopLs (Jumpi v body endLoop) pre
        let Just liveBody = annBlock post
        setLabel body liveBody
        cfg ((loop,endLoop):loopLs) (error "this is never used") post
        --Now we're not in a SLC... what should the live of irs be?
        
        
--Problem: a block of IRs must have an end :: Branch Name because pre in while
--branches to an ifte.
--However, dBlock returns a label.
{-
An if followed by an if will lead to an empty SLC... prune those later.
Consider
if(a)
 if(b)...
if(c2)...
There if(b) continues to an if, but so does the false branch of if(a).
So you can't always prune them...
-}

--Given a possibly empty block and its end label, return the label for jumping
--to it and a recipe for building the block. If the block is empty, the label
--will be the end and the recipe will do nothing.
--Note I must "declare" the block in advance of building it, because branch et
--al mean the order in which I run CFGMs matters.
{-
data Recipe = EmptyBlock
            | CookBlock Label Branch [IR Live Name]
            --Live set implicit since the list is nonempty
  deriving (Eq,Ord,Read,Show)
dBlock :: Label -> [IR Live Name] -> CFGM (Label,Recipe)
dBlock end = \case
  [] -> return (end,EmptyBlock)
  irs -> do
    l <- newLabel
    return (l,CookBlock l end irs)
cBlock :: [(Label,Label)] -> Recipe -> CFGM ()
cBlock loopLs = \case
  EmptyBlock -> return ()
  CookBlock l end irs ->
    let Just live = annBlock irs
    in do setLabel l live
          cfg loopLs (Jump end) irs
-}
branch :: Branch Name -> CFGM ()
branch b = do
  curr <- gets currentSLC
  case curr of
    Nothing -> error "Can't branch outside an SLC"
    Just (l,live,ops) -> do
      s <- get
      put s{currentSLC = Nothing,
            labelSLCMap = M.insert l (SLC {slcOps = ops,
                                           slcBranch = b,
                                           slcLive = live
                                          }) $ labelSLCMap s
           }
setLabel :: Label -> Live -> CFGM ()
setLabel lab live = do
  curr <- gets currentSLC
  case curr of
    Nothing -> do
      m <- gets labelSLCMap
      case M.lookup lab m of
        Nothing -> do
          s <- get
          put s{currentSLC = Just (lab,live,[])}
        Just _ -> error "Duplicate SLC labels"
    --This can happen at the start of a while
    Just _ -> do
      branch (Jump lab)
      setLabel lab live

appendOps :: [([Name],[Name])] -> CFGM ()
appendOps ops = do
  s <- get
  case currentSLC s of
    Nothing -> error "Can't append ops outside SLC"
    Just (lab,live,prefix) ->
      put s{currentSLC = Just (lab,live,prefix++ops)}
-}

-}
