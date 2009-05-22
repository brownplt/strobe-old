module BrownPLT.TypedJS.ReachableStatements
  ( allReachable
  ) where

import BrownPLT.TypedJS.Prelude
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive.Query.BFS (bfs)
import BrownPLT.JavaScript.Analysis.ANF

allReachable tr = foldr check (Right ()) (flatten tr)
  where check _ (Left p) = Left p
        check (_, f, gr) _ =
          case length (bfs (fst (G.nodeRange gr)) gr) == length (G.nodes gr) of
            True -> Right ()
            False -> Left (snd (funcLitX f))
