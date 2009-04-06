module TypedJavaScript.Graph 
  ( topologicalOrder
  ) where

import qualified Data.Graph.Inductive as G 
import qualified Data.Set as S
import Data.Graph.Inductive (Graph, DynGraph, Node, Edge)
import Data.Set (Set)
import Data.List
  
hasIncomingEdges :: Graph gr
                 => gr a b
                 -> Node -> Bool
hasIncomingEdges gr vx = not $ null (G.pre gr vx)

preEdges :: Graph gr
         => gr a b
         -> Node
         -> [Edge]
preEdges gr vx = map (\preVx -> (preVx, vx)) (G.pre gr vx)

delSuccs :: DynGraph gr
         => gr a b
         -> Node
         -> gr a b
delSuccs gr vx = G.delEdges (map (\succVx -> (vx, succVx)) (G.suc gr vx)) gr

cyclicTopo :: DynGraph gr
           => ([Node], -- ^Nodes with no incoming edges that may be added
                       -- to the graph
               [Node], -- ^Solution so far: reverse-topologically ordered nodes
               [Node], -- ^nodes that were restricted
               [Edge], -- ^Solution so far: edges that have been removed to
                        -- break cycles
               gr a b)
           -> ([Node], -- ^Nodes with no incoming edges that may be added
                       -- to the graph
               [Node], -- ^Solution so far: reverse-topologically ordered nodes
               [Node], 
               [Edge], -- ^Solution so far: edges that have been removed to
                        -- break cycles
               gr a b)
cyclicTopo ([], solution, [], removed, gr) = 
  ([], solution, [], removed, gr)
cyclicTopo ([], solution, restricted, removed, gr) = result where
  remaining = filter (`notElem` solution) restricted
  cycleEdges = concatMap (preEdges gr) remaining
  result = cyclicTopo (remaining, solution, [], removed ++ cycleEdges,
                       G.delEdges cycleEdges gr)
  
cyclicTopo ((node:nodes), solution, restricted, removed, gr) = result where
  succs = G.suc gr node
  gr0 = delSuccs gr node

  (restrictedHere,freed) = partition (hasIncomingEdges gr0) succs

  result = cyclicTopo (freed ++ nodes, node:solution, 
                       restrictedHere ++ restricted, removed, gr0)

-- |Given a finite set S, and an ordering relation S < S, returns the elements 
-- of S in topological order, [x0, x1, ..., xn]. For i < j, xi < xj.
-- The ordering relation is specified by a directed graph along with a
-- distinguished bottom element x0, such that x0 < xi, i > 0.
--
-- Assumes: 'root' is the only node with no incoming edges
-- Guarantees:
--   1. The nodes are in topological order in the graph where the edges are
--      are removed.
--   2. Removing the edges preserves the property that 'root' is the only
--      node with no incoming edges.
topologicalOrder :: DynGraph gr
                 => gr a b -- ^graph
                 -> Node -- ^root vertex
                 -> ([Node], [Edge]) -- ^ordered nodes and removed edges
topologicalOrder gr root = (reverse ordered, removed) where
  (fringe ,ordered, restricted, removed, gr') = 
    cyclicTopo ([root], [], [], [], gr)
