module BrownPLT.TypedJS.ReachableStatements
  ( allReachable
  ) where

import BrownPLT.TypedJS.Prelude
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive.Query.BFS (bfs)
import BrownPLT.JavaScript.Analysis.ANF
import qualified TypedJavaScript.Syntax as Stx

removeFunction :: Stx.Expression SourcePos -> Stx.Expression SourcePos
removeFunction (Stx.FuncExpr p args t body) = 
  Stx.FuncExpr p [] t (Stx.EmptyStmt p)
removeFunction e = e


isFunction :: Stx.Expression SourcePos -> Bool
isFunction (Stx.FuncExpr {}) = True
isFunction e = False

unreachableStatements :: [Stx.Statement SourcePos]
                      -> [Stx.Statement SourcePos]
unreachableStatements = do            

allReachable tr = foldr check (Right ()) (flatten tr)
  where check _ (Left p) = Left p
        check (_, f, gr) _ =
          case length (bfs (fst (G.nodeRange gr)) gr) == length (G.nodes gr) of
            True -> Right ()
            False -> Left (snd (funcLitX f))
