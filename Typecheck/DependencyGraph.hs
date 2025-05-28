{-# LANGUAGE LambdaCase #-}
module TypeCheck.DependencyGraph (buildGraph) where

import AST.DTs

import Data.Graph
import Data.Generics
import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Map (Map(..))
import qualified Data.Map as M

--Divide dynamic things into SCCs of names to be inferred together, returned
--in reverse topological order (so there are no edges from earlier sets to
--later ones).
--Consequence: when inferring an SCC, all of its subordinate dependencies
--already have tysigs.
--Dynamic things with signatures are excluded.
buildGraph :: Module -> [[Name]]
buildGraph m =
  let sigs = M.keysSet $ tysigs m
      ks f = (M.keysSet $ f m) `S.difference` sigs
      fs = ks defuns
      ss = ks static
      gs = ks globals
      relevant = S.unions [fs,ss,gs] `S.difference` sigs
      --We do *not* add a reverse edge for globals
      ment x = S.intersection relevant $ mentioned x
      getmen f = M.fromSet (\nm -> ment (f m M.! nm))
      fnms = getmen defuns fs
      snms = getmen static ss
      gnms = getmen globals gs
      (graph,v2nkks,k2mv) = graphFromMap $ M.unions [fnms,snms,gnms]
      vertexTrees = scc graph
      verticess = map (S.toList . treeVertices) vertexTrees
      nmss = do
        vs <- verticess
        return $ map (\v -> let (nm,_,_) = v2nkks v in nm) vs
  in nmss

treeVertices (Node a ts) = S.insert a $ S.unions $ map treeVertices ts

{-
graphFromPairs :: Ord k => [(k,k)] ->
                  (Graph, Vertex -> (k,k,[k]), k -> Maybe Vertex)
graphFromPairs kks =
  let k2ks = foldr (\(from,to) -> M.adjust (S.insert to) from) M.empty kks
      kkks = do
        (k,ks) <- M.toList k2ks
        return (k,k,S.toList ks)
  in graphFromEdges kkks
-}
graphFromMap :: Ord k => Map k (Set k) ->
  (Graph, Vertex -> (k,k,[k]), k -> Maybe Vertex)
graphFromMap k2ks =
  let kkks = do
        (k,ks) <- M.toList k2ks
        return (k,k,S.toList ks)
  in graphFromEdges kkks

--Names which may occur in an EVMC program:
--Static dyn things: function, static, global
--Irrelevant: constructors, fields, locals, _
--Assignment to functions or static values should be disallowed and
--Con = e turns into pattern matching, so there's no risk locals shadow other
--names.
mentioned :: Data a => a -> Set Name
mentioned = everything S.union $ mkQ S.empty (\case Var nm -> S.singleton nm
                                                    _ -> S.empty)
