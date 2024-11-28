{-# LANGUAGE LambdaCase #-}
module ToyCFG where

import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.State

--For experimenting with how to simultaneously generate CFG and tag each SLC
--with live vars.
type Name = String
--Params: annotation (() or Set v), var
data IR a v = Ops a [([v],[v])]  --ops with everything but dataflow removed
        | If a v [IR a v] [IR a v]
        | While a [IR a v] v [IR a v]
        | Return a [v] --live set implicit, but no point repeating comput'n
        | Break a Int --break to i'th loop end
        | Continue a Int --continue to i'th loop end
  deriving (Eq,Ord,Read,Show)
annotIR :: IR a v -> a
annotIR = \case
  Ops a _ -> a
  If a _ _ _ -> a
  While a _ _ _ -> a
  Return a _ -> a
  Break a _ -> a
  Continue a _ -> a
--The live of a given block
annotBlock :: [IR a v] -> Maybe a
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
                 IR () Name ->
                 (IR Live Name, Live)
annIRWithLive loopLs end =
  let rs = annIRsWithLive loopLs end in
    \case
      Ops () ops ->
        let end' = applyOps end ops
        in (Ops end' ops, end')
      If () v th el ->
        let (th',end1) = rs th
            (el',end2) = rs el
            s = S.insert v $ end1 `S.union` end2
        in (If s v th' el',s)
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
              (If () v post' [])
            --This is the final loop label
            (_,loop) = annIRsWithLive loopLs end' pre
            --While body:
            (If loopCont _ loopBody [], _) =
              annIRWithLive ((loop,end):loopLs) end (If () v post' [])
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
applyOps end = \case
  [] -> end
  (lhs,rhs):ops ->
    S.union (S.fromList rhs) $ applyOps end ops  S.\\ S.fromList lhs

annFun = annIRsWithLive [] S.empty
--Each block generates a new graph, potentially connected to the old.
--Params: live set, end branch.
--Why pass in a branch? Because if, while and return terminate the SLC
--above it.

--Some test AST combinators
x =: ws = Ops () [([x],words ws)]
ret ws = Return () $ words ws
while x = While () x
ifte x = If () x
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

data SLC v = SLC {slcOps :: [([v],[v])],
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

cfgFun :: [IR Live Name] -> CFGM (Maybe LL)
cfgFun = cfg [] Nothing

--The main, useful function
ir2cfg :: [IR () Name] -> (Maybe LL, CFGS)
ir2cfg = runCFG . cfgFun . fst . annFun
--The end label of while loops is a Maybe LL because it's a continuation.
--That solves the edge case where the while loop has no cont, but it's fine
--because the loop cond always returns.
--If either branch of an ifte returns a Nothing, generate no node and return
--a Nothing. To be well-formed, the function must return a Just.
cfg :: [(LL,Maybe LL)] -> Maybe LL -> [IR Live Name] -> CFGM (Maybe LL)
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
  Ops live ops : irs -> do
    mll' <- cfg loopLs mll irs
    case mll' of
      Nothing -> return Nothing
      Just (cont,_) -> do
        genSLC live ops (Jump cont)
  If live v th el : irs -> do
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
