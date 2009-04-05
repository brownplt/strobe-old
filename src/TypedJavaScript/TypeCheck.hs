module TypedJavaScript.TypeCheck  where

import TypedJavaScript.Prelude
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Graph.Inductive as G
import Control.Monad.State.Strict

import TypedJavaScript.Syntax (Type (..))
import TypedJavaScript.Environment
import TypedJavaScript.Types

import BrownPLT.JavaScript.Analysis.Intraprocedural (Graph,
  allIntraproceduralGraphs)
import BrownPLT.JavaScript.Analysis.ANF

data TypeCheckState = TypeCheckState {
  stateGraph :: Graph
}

type TypeCheck a = StateT TypeCheckState IO a

nodeToStmt :: G.Node -> TypeCheck (Stmt (Int,SourcePos))
nodeToStmt node = do
  state <- get
  -- Nodes are just integers, so looking up the node label can fail with an
  -- arbitrary integer.
  case G.lab (stateGraph state) node of
    Just stmt -> return stmt
    Nothing -> fail $ "nodeToStmt: not a node " ++ show node


-- |Type-check the body of a function, or the sequence of statements in the
-- top-level.
body :: Env
     -> G.Node
     -> TypeCheck ()
body env enterNode = do
  state <- get
  let gr = stateGraph gr
  unless (null $ G.pre gr enterNode) $ -- ENTER has no predecessors
    fail $ "Unexpected edges into  " ++ show (G.lab gr enterNode)

  -- Assume no cycles.  We must traverse the nodes of this function in
  -- topological order.  Since topological-sort is a generic graph algorithm,
  -- we should build it separately.
  -- 
  -- For each node N, let S = nodeToStmt S.  Apply stmt ENV N S.  ENV is the
  -- environment in which the statement is evaluated.  It is the union of the
  -- environments returned by parents(S).  Topological order ensures that
  -- we have all environments for parents(S).
  -- 
  -- However, we must store these environments in an auxilliary data structure
  -- (e.g., Map Node Env) that maps each statement to its environment.  If a
  -- new environment appears, replace the existing environment with the union of
  -- the current and previous environment (see Data.Map.unionWith).
  --
  -- Consider cycles.  Break cycles at the "bottom" of loops.  More precisely,
  -- note that there are no edges out of enterNode, so all edges incidect on
  -- enterNode are directed outward.  In an acyclic graph, enterNode is the
  -- only node where all edges are directed outward.  Break cycles so that
  -- enterNode remains the only node where all edges are directed outward.
  --
  -- Keep track of the edges that are removed.  As a first approximation, we can
  -- simple ensure that the environment at the source and destination of each
  -- removed edge is identical: an iteration of the loop does not effect the
  -- environment in any way regardless of breaks, continues, etc.  If we find
  -- this too restrictive, we can write a more sophisticated system.

  (nodes,removedEdges) <- topologicalOrder gr node

  
  
  

stmt :: Env -- ^the environment in which to type-check this statement
     -> G.Node -- ^the node representing this statement in the graph
     -> Stmt (Int,SourcePos)  -- ^the statement itself
     -> TypeCheck [(G.Node,Env)] -- ^maps successors to environments

expr :: Env -- ^the environment in which to type-check this expression
     -> Type SourcePos -- ^the type of this expression

-- |When a node has multiple parents, this function combines their environments.
unionEnv :: Env -> Env -> Env

