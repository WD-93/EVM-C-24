{-# LANGUAGE LambdaCase #-}
module CFG where

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad (replicateM)
import Control.Monad.State
import Control.Applicative ((<|>))
import Data.Graph

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
type Label = Int
data Branch = BReturn [Name] --includes ret as the first word argument
            --(after mem et al)
            | BTailCall Name [Name] --includes ret as the last argument
            | Jump Label --a static jump to a label
            | Jumpi Name Label Label --ifte cond then else
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
startNewSLC :: Label -> CFG ()
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
newCFGLabel :: CFG Label
newCFGLabel = do
  s <- get
  let n = cfgLabelCtr s
  put s{cfgLabelCtr = n + 1}
  return n

--Transformations: tree shake (transitive closure of jumps-to from 0).
--Build graph with node -> slc, parents, children
--For each node, associate with live = used vars of all descendants
--Opt: follow through empty SLCs, a -> {} -> b => a -> b.
--When compiling to stack-aware code, if a ends with an ifte then a new
--stack-aware SLC that adjusts a's layout for b may be inserted.

--Using Data.Graph makes sense... but I don't like that the vertex -> node and
--node -> Maybe vertex functions aren't persistent. Well, I could build maps
--to serialize them if it comes up; otherwise I package graphs with their
--accessors.
--Without tree shaking, the list of valid keys is contiguous 0..n.
--I'll just use Map...

--Given a node, return the labels it might jump to
slcChildren :: SLC -> [Label]
slcChildren (_,branch) =
  case branch of
    Jump l -> [l]
    Jumpi _ l1 l2 -> [l1,2]
    _ -> []

-- ****************************************************************************
--Using Data.Graph instead of custom code...
type GWithOps = (Graph, Vertex -> (SLC, Label, [Label]), Label -> Maybe Vertex)
fromEdges :: Map Label SLC -> GWithOps
fromEdges = graphFromEdges . map (\(l,slc) -> (slc,l,slcChildren slc)). M.toList

treeShake :: GWithOps -> GWithOps
treeShake (g,v2n,k2v) =
  let Just v0 = k2v 0 --the function start, always present
      vs = reachable g v0
  in graphFromEdges $ map v2n vs

--Now to compute live vars...
--Live (node) = vars used by node and descendants
--"and descendants" is just reachable... but I can use SCCs instead
--Each SCC is a tree; all vertices in an SCC have the same live vars.
--The set of vs reachable from an SCC is the union of the out-dests of all
--its nodes.
--It's the SCC pointed to that matters; associate each vertex with the index
--of its SCC.
--The SCCs are conveniently returned in reverse topological order; associate
--each with its live set.
--Live (SCC) = union of live of each SLC in it U live of its child SCCs
--For each SCC, associate its labels with the SCC's live.
{-
liveVars :: GWithOps -> (Map Vertex Int, Map Int (Set Name))
liveVars (g,v2n,k2mv) =
  let sccs = scc g --the SCCs of g
      --associate each SCC with an index
      --for each SCC, associate each node in it with its index
      v2SCCIxMap = M.fromList $ do
        (ix,sc) <- zip [0..] sccs
        v <- flattenSCC sc
        return (v,ix)
      vSCC v = case M.lookup v v2SCCIxMap of
                 Just ix -> ix
                 Nothing -> error "Something went horribly wrong!"
      --Given a vertex, get SCCs referred to (including own SCC)
      v2ChildSCCs v = let (_,_,vs) = v2n v
                      in S.fromList $ map vSCC vs
      
  in (v2SCCIxMap, undefined)
-}

--Not maximally general, but good enough for my purposes
foldOverSCCs :: (Tree node -> [a] -> a) -> --folding function
                (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex) ->
                --A general graph
                a
foldOverSCCs f (g,v2n,k2mv) =
  let sccs = scc g
      isccs = zip [0..] sccs
      --Associate each vertex with its SCC index
      v2ixMap = M.fromList $ do
        (i,sc) <- isccs
        v <- flattenSCC sc
        return (v,i)
      v2ix v = case M.lookup v v2ixMap of
                 Just ix -> ix
                 --All vertices are in some SCC...
                 Nothing -> error "Something went horribly wrong!"
  in undefined
--Note the branch can also use vars
liveVarsSLC :: SLC -> Set Name
liveVarsSLC (ops,branch) =
  S.fromList $ (ops >>= \(_ := (_,args)) -> args) ++
  case branch of
    BReturn vs -> vs
    BTailCall f vs -> f:vs
    Jump l -> [] --constant label
    Jumpi cond _ _ -> [cond] --only cond is a var, labels are constant
  

-- ****************************************************************************
{-    
treeShake :: Map Int SLC -> Map Int SLC
treeShake m = M.restrictKeys m (reachableFrom slcChildren 0 m)
{-
Algo:
s = {}
explore k:
 if k in s: return ()
 put k in s
 mapM explore $ keys k
-}
reachableFrom :: Ord k => (v -> [k]) -> k -> Map k v -> Set k
reachableFrom f k m = flip execState S.empty $
  explore (\k -> case M.lookup k m of
              Nothing -> error "Smth went terribly wrong (incomplete graph)"
              Just v -> f v
          ) k
explore :: Ord k => (k -> [k]) -> k -> State (Set k) ()
explore f k = do
  s <- get --accidental pun
  if S.member k s
    then return ()
    else do
    put $ S.insert k s
    let ks = f k
    mapM_ (explore f) ks

edges :: Map Int SLC -> [(Int,Int)]
edges m = do
  (from,v) <- M.toList m
  to <- slcChildren v
  return (from,to)

--For each (from,to), insert to into m[from] (Nothing means {})
edgesToGraph :: Ord k => [(k,k)] -> Map k (Set k)
edgesToGraph = foldr (\(from,to) -> M.alter (ins to) from) M.empty
  where
    ins k ms = (S.insert k <$> ms) <|> Just (S.singleton k)

parentGraph :: Map Int SLC -> Map Int (Set Int)
parentGraph = edgesToGraph . map (\(from,to) -> (to,from)) . edges

--OK, now I've tree shaken and obtained parents... what next?
--Need live vars for each node.
--I need a DS to maintain the invariants when I modify nodes...
--Nodes disconnected from the graph should be deleted.
--Simplifications:
--ifte cond th th => jump th
--ex: if cond {} {} => cond;
--a jump-> {} branch => a branch, delete {}
--subgraph with no leaves: revert
--When deleting a node, decrement the refcount of its children
--Refcounting makes treeShake redundant...
--Conversely, when modifying a node (redirecting it for example), dec and inc
--refcounts.
data GraphNode = GraphNode {
  gnParents :: Set Label,
  gnSLC :: SLC,
  gnChildren :: Set Label
  }
  deriving (Eq,Ord,Read,Show)
--Invariants:
--1) refcount (S.size . gnParents) > 0 for all nodes
--2) for each ref (from,to), both from and to are in the graph and
--g[from].children contains to, g[to].parents contains from
--3) for each g[l] in graph, g[l].children = S.fromList (slcChildren g.slc)
--4) The graph includes label 0 (function start).
--Bidirectional graph
type BGraph = Map Int GraphNode

buildGraph :: Map Label SLC -> BGraph
buildGraph m =
  let es = edges m
      chs = edgesToGraph es
      ps = edgesToGraph $ map (\(from,to) -> (to,from)) es
  in M.fromList [(l,GraphNode p slc c)
                | (l,slc) <- M.toList m,
                  let Just p = M.lookup l ps,
                  let Just c = M.lookup l chs,
                  --We don't include nodes with refcount 0
                  S.size p > 0
                ]
--Problem: live is also updated whenever the graph is modified...
--Easy but slow solution: recompute as needed.
--Is $mem always live? No, not in functions which don't modify memory (FW),
--nor in invalid(). It is live in RETURN and revert because they use memory,
--but not in stop().
{-
For each node, return the set of vars which may be used in subsequent nodes.
First divide into SCCs; the resulting SCC graph is a DAG, at which point
--folding over it can be done straightforwardly, with memo to opt sharing.
-}
liveVars :: BGraph -> Map Label (Set Name)
liveVars = undefined

--SCC algo:
--Incrementally build a tree of SCCs
--Explore them; each candidate SCC has a path from root. Associate nodes with
--the SCC that contains them.
--If you find an edge to a node in an SCC in your path, you've found a cycle;
--merge the SCCs. The new SCC has the union of the members, out-edges and
--in-edges.
--In DFS, does the path behind you change as you explore?
-}
