module Opt.Analysis.Exitness where

import Opt.Semilattice
import Core.RestrictedCore
import Core.SSA (OptCore())
import Opt.AI hiding (unsafePrint,debugFlag)
import Opt.HTraversable (Id(..))
import Util (unsafePrint')

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Arrow ((***))

debugFlag = False
unsafePrint str = unsafePrint' debugFlag str

--A module for determining whether each BB may exit or return;
--a BB which may do neither is divergent and can be replaced with
--revertValue().
--Doing so is essential for eta reduction, since otherwise there might be
--cycles of eta-reducible BBs which could not be safely deleted after
--substitution.

--Since may exit dominates may return, they can be in the same join semilattice
--value. NB: return refers to C function return, not EVM RETURN (which is an
--exit).
data Exitness = Bottom | MayReturn | MayExit
  deriving (Eq,Ord,Read,Show)
instance JoinSemilattice Exitness where
  (\/) = max
instance HasBottom Exitness where
  bottom = Bottom
--Eta-reducible functions may form cycles, so need to replace divergent BBs
--with reverts first.
--Need to be more precise than following succs without regard for
--call/return: consider
--f() := h();
--g() := while (True) h()
--h() := {}
--Looking only at succs, it appears as if g might terminate because h's
--return continuation includes a BB in f.
--exitness[f] where f lhs = call G,args,Ret =
--may exit if any g <- G may exit \/
--lub exitness[r] for ret <- Ret if any g <- G may return
--A badfun may exit; as such it's irrelevant that it also may return.
--A returning jump may return, but not exit.
--An exit may exit but not return. Note revert /= divergence; a program
--diverges if it loops infinitely, at which point it'll inevitably run out of
--gas and effectively revertValue().
--All other branches have exitness = lub of succs
--Does divergence analysis need to be shared? The CFG and call graph could be
--relevant to inlining (for DFS).

{-
exitness = transitive closure of base cases + lub
Consider a -> b or c, b -> a, c exits.
b may exit, but a naive DFS would find a was already explored and need to make
a guess without knowing about c.
Tracking unexplored edges per node could solve that, but instead I'll use a
callback-based approach a la AI but with inspectable state and run queue.

Algo:
Initial state: Bottom, no callbacks for all BBs
For each BB, set callbacks on relevant children and set lattice value
(triggering callbacks).
Callbacks and tasks on runqueue are defunctionalized.

NB: this algo tolerates calls into any BB of another C function, so it's
compatible with interprocedural inlining.
-}
analyzeExitness :: FrozenModState -> OptCore -> Map FunVar Exitness
analyzeExitness ms core =
  M.map fst $ exitness $ execState (runReaderT go (ms,core)) initState
  where initState = AES {exitness = M.map (const (Bottom, [])) $ funInfo ms,
                         alreadyReturning = S.empty,
                         aesRunQueue = []
                        }
        go = do
          unsafePrint "Start analyzeExitness!"
          forM_ (M.toList $ funInfo ms) $
            uncurry handleFun
          aemScheduler
--Cases: call, return, exit, normal (other branch including JT)
handleFun :: FunVar -> FrozenFunInfo -> AEM ()
handleFun f fi = do
  unsafePrint $ "handleFun " ++ f
  case fiBodyInfo fi of
    IsJT -> handleNormal f $ unId $ succs fi
    IsFun {fiVars = v2av} -> do
      defs <- asks $ coreDefuns . snd
      case M.lookup f defs of
        Nothing -> error "!?"
        Just (_lhs,(_ops,branch)) ->
          case branch of
            --succs branch types: normal, continues
            --if g is normal, it's a callee
            --if r is continues, it's a return cont
            --Ignore the possibility of coerced funs with bad arity
            --If the callee may be a badfun, the caller may exit
            Jump (Calling _) _ -> do
              unsafePrint (f ++ " calls")
              if not $ M.null $ unId $ badFunSuccs fi
                then set f True
                else let gs = M.keys $ M.filter (==Normal) $ unId $ succs fi
                     in forM_ gs (`calledBy` f)
            Jump Returning _ -> unsafePrint (f++" returns") >> set f False
            Stop _ -> unsafePrint (f++" stops") >> set f True
            Revert _ -> unsafePrint (f++" reverts") >> set f True
            Return _ -> unsafePrint (f++" RETURNs") >> set f True
            _ -> do
              unsafePrint (f++" is normal")
              handleNormal f $ unId $ succs fi
--The default rule: f >= its successors
--Since f is not a call, it won't have any continues successors or
--badfun succs.
handleNormal :: FunVar -> Map FunVar BranchType -> AEM ()
handleNormal f f2bt = mapM_ (`lessThan` f) $ M.keys f2bt
aemScheduler :: AEM ()
aemScheduler = do
  rq <- gets aesRunQueue
  case rq of
    [] -> unsafePrint "All done!" >> return ()
    (f,b):rq' -> do
      let e' = bool2exitness b
      unsafePrint $ f ++ " >= " ++ show e'
      modify (\aes->aes{aesRunQueue = rq'})
      --Fetch callbacks and run each if f modified
      m <- gets exitness
      case M.lookup f m of
        Just (e,cbs) ->
          if e' > e
          then do
            --Forgot to actually update exitness!
            setExitness f e'
            mapM_ (\cb -> do
                            unsafePrint $ "Triggered: " ++ show cb 
                            runCallback b cb) cbs
          else return ()
        Nothing -> error "!?"
      aemScheduler
runCallback b cb =
  case cb of
    LessThan g -> set g b
    CalledBy f ->
      if b
      then set f True
      else lubRet f
--lubRet f = f >= r for r <- Ret where f = call G,args,Ret
lubRet :: FunVar -> AEM ()
lubRet f = do
  --Mark f as already returning so >= callbacks aren't added for each
  --returning g <- G
  ar <- gets alreadyReturning
  if S.member f ar
    then return ()
    else do
    modify (\aes->aes{alreadyReturning = S.insert f ar})
    --Look up return continuations in ms
    ms <- asks fst
    let Just fi = M.lookup f $ funInfo ms
        rs = M.keys $ M.filter (/=Normal) $ unId $ succs fi
    forM_ rs (`lessThan` f)
bool2exitness b = if b then MayExit else MayReturn
--Rules may be immediately triggered by the exitness they subscribe to; these
--combinators handle that.
lessThan :: FunVar -> FunVar -> AEM ()
f `lessThan` g =
  if f == g --Can occur in self-jumps
  then return ()
  else do
    e <- getExitness f
    case e of
      MayExit -> set g True
      MayReturn -> set g False >> register f (LessThan g)
      _ -> register f (LessThan g)
calledBy :: FunVar -> FunVar -> AEM ()
g `calledBy` f =
  if f == g --Then f/g is divergent
  then return ()
  else do
    e <- getExitness g
    case e of
      MayExit -> set f True
      MayReturn -> lubRet f >> register g (CalledBy f)
      _ -> register g (CalledBy f)

getExitness :: FunVar -> AEM Exitness
getExitness f = do
  m <- gets exitness
  case M.lookup f m of
    Just (e,_) -> return e
    Nothing -> error "!?"
--Sets exitness without triggering any callbacks. Should only be used to
--increase it! Precondition: the key exists.
setExitness :: FunVar -> Exitness -> AEM ()
setExitness f e = modify (\aes->aes{exitness = M.adjust (const e *** id) f $
                                     exitness aes})
--Callbacks on exitness[f]
--Each callback is implicitly parameterized its f
--They're run in sequence; there's no need to unregister them since they're
--run at most twice.
data AECallback = LessThan FunVar --x >= y
                | CalledBy FunVar
  deriving (Eq,Ord,Read,Show)
type AETask = (FunVar,Bool) --False: MayReturn, True: MayExit
type AEM = ReaderT (FrozenModState,OptCore) (State AES)
data AES = AES {exitness :: Map FunVar (Exitness,[AECallback]),
                --For f lhs = call G,arg,Ret, the f >= ret <- Ret rule should be
                --triggered only the first time some g <- G is found to may
                --return. That means the fs for which it has been triggered
                --needs to be tracked.
                alreadyReturning :: Set FunVar,
                aesRunQueue :: [AETask]
               }
  deriving (Eq,Ord,Read,Show)
--Note: tasks only run in sequence.
--x <= y => on x modified, y \/= x.

--may exit if any g <- G may exit \/
--lub exitness[r] for r <- Ret if any g <- G may return (f) =>
--for each g <- G:
-- on g = e --either may return or may exit
-- if e = may exit: f may exit
-- else:
--  for each r <- Ret, r >= f

--You only need to set to a value > bottom. False: may return, True: may exit
--Schedules an assignment; the order in which they're run doesn't matter.
set :: FunVar -> Bool -> AEM ()
set f mayExit =
  modify (\aes->aes{aesRunQueue = (f,mayExit) : aesRunQueue aes})

--Register callback. Precondition: the key is present.
register :: FunVar -> AECallback -> AEM ()
register f cb =
  modify (\aes->aes{exitness = M.adjust (id *** (cb:)) f $ exitness aes})
