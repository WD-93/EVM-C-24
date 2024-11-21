{-# LANGUAGE LambdaCase #-}
module CFG where

import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad (replicateM)
import Control.Monad.State

import DTs (Name(..))
import IR1
--Here we break up structured IR into a CFG, then do SSA.
--Branch type: return, jump, jumpi, diverge.
--CFG node props: live @ start (un-indexed vars),
--vars assigned, vars used.

--First: CFG.
--Need: an anon label pool. When generating a CFG for a function, only label
--0 will be externally reachable... but we don't need to care about that here.
type CFG = State CFGS --no risk of error
data CFGS = CFGS {cfgLabelCtr :: Int,
                  cfgCurrentLabel :: Maybe Int,
                  cfgInstrAccumulator :: [IR], --for accumulating a SLC
                  cfgLabelSLCMap :: Map Int SLC
                   --live vars etc added later
                 }
  deriving (Eq,Ord,Read,Show)
--Invariant: the IRs are all ops
type SLC = ([IR],Branch)
data Branch = BReturn [Name] --includes ret as the first word argument
            --(after mem et al)
            | BTailCall Name [Name] --includes ret as the last argument
            | Jump Int --a static jump to a label
            | Jumpi Name Int Int --ifte cond then else
            --a choice; the else branch is placed directly afterward.
  deriving (Eq,Ord,Read,Show)
--Given a compiled function block, divide it into a CFG.
--Assume that we've already inserted a return at the end, so we won't fall
--through off the end of the function.
--When should I do that? At the IR compilation level; I need to know the
--return type to generate soft coerce (conversion) code for returns anyway.
--Alt: do it at the C level by appending return (returnType) ()
--Explicit coercion should be able to handle any two types.
{-
if(cond) th el =>
l1, l2, end <- new
branch (Jumpi cond l1 l2)
l1: th, jump end
l2: el, jump end
end:

Invariant: else branches always have only one parent, so their stack layout
doesn't change and you can replace the jump with a fallthrough.
-}
{-
On end param:
In ifte cond th el, th and el should branch to end if they fall through.
cond should also be able to diverge.
Should individual ops be able to branch? stop, jump et al... then I'd need
a branch type for them, but that makes sense.
Overloaded functions for RETURN would be nice, but requires separate type
checking from codegen.
I need a handler for [] in cfg to implement the default jump.
Note the stop branch should not take mem as a param, since further writes
don't matter. jump should take all state, however.
revert should take no state params, as it's all reverted.
What should be the end param for the top-level block? It can be an error
value, the top-level block should always terminate with a leaf branch anyway.
-}
cfg :: Branch -> [IR] -> CFG ()
cfg end = \case
  [] -> branch end
  ir:irs ->
    case ir of
      Ifte v th el -> do
        xs <- replicateM 3 newCFGLabel
        let [the,els,end'] = xs
        branch (Jumpi v the els)
        startNewSLC the
        cfg (Jump end') th
        startNewSLC els
        cfg (Jump end') el
        startNewSLC end'
        cfg end irs
      While pre v post -> do
        xs <- replicateM 3 newCFGLabel
        let [loop,loopCont,end'] = xs
        startNewSLC loop
        cfg (Jumpi v loopCont end') pre
        startNewSLC loopCont
        cfg (Jump loop) post
        startNewSLC end'
        cfg end irs
      DoWhile body post var -> do
        loop <- newCFGLabel
        cond <- newCFGLabel
        end' <- newCFGLabel
        startNewSLC loop
        cfg (Jump cond) body
        startNewSLC cond
        cfg (Jumpi var loop end') post
        startNewSLC end'
        cfg end irs
      --Branching statements terminate the SLC
      Return vs -> branch (BReturn vs)
      TailCall f vs -> branch (BTailCall f vs)
      --Add an instruction to the current SLC
      op@(:=){} -> addIR op >> cfg end irs
buildCFG :: [IR] -> CFGS
buildCFG irs = execState (do l <- newCFGLabel
                             cfg err irs)
               CFGS{cfgLabelCtr = 0,
                    cfgCurrentLabel = Nothing,
                    cfgInstrAccumulator = [],
                    cfgLabelSLCMap = M.empty}
  where err = error $ "Function doesn't branch in all paths: " ++ show irs
  --A compromise compilation, trading off perf vs code size:
  --We first jump to the cond check (adding a JUMPDEST per iteration),
  --then do one branch per loop iteration.
  --No, that won't work... naive jump elimination will convert the first
  --jump to a fallthrough and then I'm left with two branches per iteration
  --anyway.
  --The pre will usually be short... better to duplicate it.
  --Temporary solution: I'll just have 2 branches...
  --In future: generate DoWhile in IR1
  --I can't duplicate exprs here because it would duplicate anon var writes

  --What happens in
  --do {return 1} while (cond)?
  --There'll be no edge to end... need to check I'm in a SLC
  --What happens if there's a stop() in the cond?
  --With do blocks even exprs could exhibit structured control flow...
  --Do I need a default end param?
  


--Add an IR op to the current SLC; only ops are acceptable.
--Errors if there is no current SLC.
addIR :: IR -> CFG ()
addIR op@(:=){} = do
  s <- get
  case cfgCurrentLabel s of
    Just l -> 
      put s{cfgInstrAccumulator = op : cfgInstrAccumulator s}
    Nothing ->
      error "Attempted to emit op outside a SLC"
--Flushes the old SLC and sets the branch. Nulls the SLC so any attempt to
--append instructions will fail until a new SLC is set.
branch :: Branch -> CFG ()
branch b = do
  s <- get
  case cfgCurrentLabel s of
    Just l -> put s{
      cfgCurrentLabel = Nothing,
      cfgInstrAccumulator = [],
      cfgLabelSLCMap = M.insert l
        (reverse $ cfgInstrAccumulator s, b) $ cfgLabelSLCMap s
      }
    Nothing -> error "This shouldn't happen"
--Sets the context to a new SLC; if there is a current SLC being accumulated
--then it's terminated with a jump to the new one.
--Overwriting an old SLC is not allowed.
startNewSLC :: Int -> CFG ()
startNewSLC l = do
  s <- get
  case cfgCurrentLabel s of
    Just l' -> do
      branch (Jump l)
      startNewSLC l
    Nothing -> put s{cfgCurrentLabel = Just l,
                     cfgInstrAccumulator = [] --just to be safe
                    }
--With lenses I'd be able to write the many instances of this pattern more
--efficiently...
newCFGLabel :: CFG Int
newCFGLabel = do
  s <- get
  let n = cfgLabelCtr s
  put s{cfgLabelCtr = n + 1}
  return n
