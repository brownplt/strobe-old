module BrownPLT.TypedJS.ReachableStatements
  ( unreachableStatements
  ) where

import BrownPLT.TypedJS.Prelude
import qualified Data.Set as S
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive.Query.BFS (bfs)
import BrownPLT.JavaScript.Analysis
import BrownPLT.JavaScript.Analysis.Intraprocedural
import BrownPLT.JavaScript.Analysis.ANF
import qualified BrownPLT.TypedJS.Syntax as Stx

unreachableInGraph :: Graph -> [Stmt (Int, SourcePos)]
unreachableInGraph gr = map lab (S.toList nodes)
  where nodes = (S.fromList $ G.nodes gr) `S.difference` 
                (S.fromList $ bfs (fst $ G.nodeRange gr) gr)
        lab node = case G.lab gr node of
          Just s -> s
          Nothing -> error "unreachableInGraph: node without a statement"
  

unreachableStatements :: ([(Id, SourcePos)], [Stmt SourcePos])
                      -> [SourcePos]
unreachableStatements anf = map (snd.label) unreachableInANF
  where unreachableInANF = concatMap unreachableInGraph graphs
        (_, tree) = allIntraproceduralGraphs anf
        graphs = map (\(_, _, gr) -> gr) (flatten tree)
