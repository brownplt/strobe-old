module TypedJavaScript.Graph where

import qualified Data.Graph.Inductive as G 
import qualified Data.Set as S
import Data.Graph.Inductive (DynGraph,Node)
import Data.Set (Set)
import Data.List

topo :: DynGraph gr
     => Node -- ^ a node with no incoming edges
     -> (gr a b, [Node]) -- ^the graph and the reverse-topologically ordered 
                         -- list of nodes so far
     -> (gr a b, [Node]) -- ^the reverse-topologically ordered list of nodes
                         -- reachable from 'node'.
topo node (gr, solution) = (gr'', solution') where
  succs = G.suc gr node
  gr' = G.delEdges (map (\succ -> (node, succ)) succs) gr

  -- Remove all edges incident and outgoing from 'node'.  Any successors that
  -- of 'node' that have no other incoming edges are topological succesors of
  -- 'node'.
  hasIncomingEdges :: Node -> Bool
  hasIncomingEdges n = not $ null (G.pre gr' n)
  (restrictedSuccs, freeSuccs) = partition hasIncomingEdges succs
  
  -- Traverse 'freeSuccs' depth-first.
  (gr'', solution') = foldr topo (gr', node:solution) freeSuccs
  

