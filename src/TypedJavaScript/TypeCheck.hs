module TypedJavaScript.TypeCheck  where

import TypedJavaScript.Prelude
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Graph.Inductive as G
import Control.Monad.State.Strict
import qualified TypedJavaScript.Syntax as TJS
import TypedJavaScript.Syntax (Type (..))
import TypedJavaScript.Environment
import TypedJavaScript.Types
import TypedJavaScript.Graph
import BrownPLT.JavaScript.Analysis (jsToCore, simplify)
import BrownPLT.JavaScript.Analysis.Intraprocedural (Graph,
  allIntraproceduralGraphs)
import BrownPLT.JavaScript.Analysis.ANF
import TypedJavaScript.ErasedEnvTree

import TypedJavaScript.TypeErasure


import qualified Data.GraphViz as GV

data TypeCheckState = TypeCheckState {
  stateGraph :: Graph,
  stateEnvs :: Map Int Env
}


type TypeCheck a = StateT TypeCheckState IO a


nodeToStmt :: G.Node -> TypeCheck (Stmt (Int,SourcePos))
nodeToStmt node = do
  state <- get
  -- Nodes are just intstateEnvs = M.emptyegers, so looking up the
  -- node label can fail with an arbitrary integer.
  case G.lab (stateGraph state) node of
    Just stmt -> return stmt
    Nothing -> fail $ "nodeToStmt: not a node " ++ show node


lookupLocalEnv :: G.Node -> TypeCheck Env
lookupLocalEnv node = do
  state <- get
  case M.lookup node (stateEnvs state) of
    Nothing -> return emptyEnv
    Just env -> return env

updateLocalEnv :: (G.Node, Env) -> TypeCheck ()
updateLocalEnv (node, incomingEnv)= do
  state <- get
  let result = M.insertWith unionEnv node incomingEnv (stateEnvs state)
  put $ state { stateEnvs = result } 

enterNodeOf :: Graph -> G.Node
enterNodeOf gr = fst (G.nodeRange gr)

exitNodeOf :: Graph -> G.Node
exitNodeOf gr = snd (G.nodeRange gr)

body :: Env
     -> ErasedEnv
     -> Type SourcePos
     -> G.Node
     -> TypeCheck Env
body env ee rettype enterNode = do
  state <- get
  let gr = stateGraph state
  unless (null $ G.pre gr enterNode) $ -- ENTER has no predecessors
    fail $ "Unexpected edges into  " ++ show (G.lab gr enterNode)

  let (nodes,removedEdges) = topologicalOrder gr enterNode

  mapM_ (stmtForBody env rettype) nodes

  finalLocalEnv <- lookupLocalEnv (exitNodeOf gr)
  return finalLocalEnv
  -- TODO: account for removedEdges

stmtForBody :: Env -- ^environment of the enclosing function for a nested
                   -- function, or the globals for a top-level statement or
                   -- function
            -> Type SourcePos
            -> G.Node
            -> TypeCheck ()
stmtForBody enclosingEnv rettype node = do
  localEnv <- lookupLocalEnv node
  s <- nodeToStmt node
  succs <- stmt (M.union localEnv enclosingEnv) rettype node s
  mapM_ updateLocalEnv succs
    
stmtSuccs :: G.Node -> TypeCheck [G.Node]
stmtSuccs stmtNode = do
  state <- get
  return (G.suc (stateGraph state) stmtNode)

stmt :: Env -- ^the environment in which to type-check this statement
     -> Type SourcePos
     -> G.Node -- ^the node representing this statement in the graph
     -> Stmt (Int, SourcePos)
     -> TypeCheck [(G.Node, Env)]
stmt env rettype node s = do
  succs <- stmtSuccs node
  -- statements that do not affect the incoming environment are "no-ops"
  let noop = return (zip succs (repeat env))
  case s of
    EnterStmt _ -> noop
    ExitStmt _ -> noop
    SeqStmt{} -> noop
    EmptyStmt _ -> noop
    AssignStmt _ v e -> do
      te <- expr env e
      case M.lookup v env of
        Nothing -> fail $ "undeclared id: " ++ show v
        Just Nothing -> do
          let env' = M.insert v (Just te) env
          return $ zip succs (repeat env')
        Just (Just t) | t == te -> noop
                      | otherwise ->
          fail $ "types not invariant: " ++ show t ++ " " ++ show te
    DirectPropAssignStmt _ obj method e -> undefined
    IndirectPropAssignStmt _ obj method e -> fail "obj[method] NYI"
    DeleteStmt _ r del -> fail "delete NYI"
    NewStmt{} -> fail "NewStmt will be removed from ANF"
    CallStmt _ result fn args -> undefined
    IfStmt _ e s1 s2 -> undefined -- the callee of stmt must ensure that all children are
                        -- accounted for
    WhileStmt _ e s -> do
      expr env e -- this permits non-boolean tests
      noop -- Will change for occurrence types
    ForInStmt _ id e s -> fail "ForIn NYI"
    TryStmt _ s id catches finally  -> fail "TryStmt NYI"
    ThrowStmt _ e -> do
      expr env e
      noop
    ReturnStmt _ Nothing 
      | rettype == undefType -> noop
      | otherwise -> fail $ "expected return value, returning nothing"
    ReturnStmt _ (Just e) -> do
      te <- expr env e
      unless (te == rettype) $
        fail $ printf "expected return %s, got %s" (show rettype) (show te)
      noop
    LabelledStmt _ _ _ -> noop
    BreakStmt _ _ -> noop
    ContinueStmt _ _ -> noop
    SwitchStmt _ _ cases default_ -> undefined

expr :: Env -- ^the environment in which to type-check this expression
     -> Expr (Int,SourcePos)
     -> TypeCheck (Type SourcePos) -- ^the type of this expression
expr env e = case e of 
  VarRef _ id -> case M.lookup id env of
    Nothing -> fail $ "unbound id: " ++ show id
    Just Nothing -> fail $ "type might be undefined or something, go away"
    Just (Just t) -> return t
  DotRef{} -> fail "NYI"
  BracketRef{} -> fail "NYI"
  OpExpr _ f args -> fail "NYI" -- perator f args
  Lit (StringLit (_,a) _) -> return $ TId a "string"
  Lit (NumLit (_,a) _) -> return $ TId a "double"
  Lit (IntLit (_,a) _) -> return $ TId a "int"
  Lit (BoolLit (_,p) _) -> return $ TId p "bool"
  Lit (NullLit (_,p)) -> fail "NullLit NYI (not even in earlier work)"
  Lit (ArrayLit (_,p) es) -> do
    -- TODO: Allow subtyping
    ts <- mapM (expr env) es
    if (length (nub ts) == 1) 
      then return (TApp p (TId p "Array") [head ts])
      else fail "array subtyping NYI"
  Lit (ObjectLit _ props) -> fail "object lits NYI"
  

-- |When a node has multiple parents, this function combines their environments.
unionEnv :: Env -> Env -> Env
unionEnv = undefined

uneraseEnv :: Env -> ErasedEnv -> Lit (Int, SourcePos) -> (Env, Type SourcePos)
uneraseEnv env ee (FuncLit (_, pos) args locals _) = (env', rettype) where
  functype = head $ ee ! pos
  Just (_, cs, types, rettype, lp) = deconstrFnType functype
  argtypes = zip (map fst args) (map Just types)
  localtypes = map (\(name,(_, pos)) -> (name, liftM head (M.lookup pos ee))) 
                   locals
  env' = M.union (M.fromList (argtypes++localtypes)) env 
uneraseEnv env ee _ = error "coding fail - uneraseEnv given a function-not"

typeCheckProgram :: Env
                  -> (Tree ErasedEnv, 
                      Tree (Int, Lit (Int,SourcePos), Graph))
                  -> TypeCheck Env
typeCheckProgram env (Node ee subEes, Node (_, lit, gr) subGraphs) = do
  state <- get
  put $ state { stateGraph = gr, stateEnvs = M.empty }
  -- When type-checking the body, we assume the declared types for functions.
  let (env', rettype) = uneraseEnv env ee lit
  topLevelEnv <- body env' ee rettype (enterNodeOf gr)
  -- When we descent into nested functions, we ensure that functions satisfy
  -- their declared types.
  -- This handles mutually-recursive functions correctly.  
  unless (length subEes == length subGraphs) $
    fail "erased env and functions have different structures"
  mapM_ (typeCheckProgram env') (zip subEes subGraphs)
  return topLevelEnv

-- |Type-check a Typed JavaScript program.  
typeCheck :: [TJS.Statement SourcePos] -> IO Env
typeCheck prog = do
  -- Build intraprocedural graphs for all functions and the top-level.
  -- These graphs are returned in a tree that mirrors the nesting structure
  -- of the program.  The graphs are for untyped JavaScript in ANF.  This
  -- conversion to ANF does not change the function-nesting structure of the
  -- original program.  For now, we assume that the conversion to ANF preserves
  -- the type structure of the program.
  let (topDecls, anfProg) = jsToCore (simplify (eraseTypes prog))
  let (anf, intraprocs) = allIntraproceduralGraphs (topDecls, anfProg)
  -- Since all type annotations are erased in the previous step, map locations
  -- to type annotations, so they may be recovered later.  The locations are
  -- that of identifiers that had type annotations, functions that had type
  -- annotations, object fields that had type annotations.
  --
  -- These "erased environments" are returned in a tree with the same shape as
  -- 'intraprocs' above.
  let envs = buildErasedEnvTree prog
  let globalEnv = M.empty -- TODO: Create file specifying global environment
  (env, state) <- runStateT (typeCheckProgram globalEnv (envs, intraprocs)) 
                            (TypeCheckState G.empty M.empty)
  return env

