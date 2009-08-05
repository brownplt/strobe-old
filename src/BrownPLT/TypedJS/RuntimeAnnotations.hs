-- |The dataflow analysis algorithm @localTypes@ is defined over A-normalized
-- JavaScript.  This module applies its results to Typed JavaScript.
module BrownPLT.TypedJS.RuntimeAnnotations 
  ( runtimeAnnotations
  , topLevelRuntimeAnnotations
  ) where

import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.LocalFlows
import BrownPLT.TypedJS.TypeDefinitions
import BrownPLT.JavaScript.Analysis
import BrownPLT.JavaScript.Analysis.Intraprocedural (numberStmts, intraproc)
import qualified BrownPLT.TypedJS.Syntax as Stx
import BrownPLT.TypedJS.TypeErasure
import qualified Data.Map as M
import Control.Monad.Error
import Control.Monad.Identity
import BrownPLT.TypedJS.TypeTheory (runtime)

type M a = ErrorT String Identity a



type Env = Map (Id, SourcePos) RuntimeTypeInfo


empty :: Map (Id, SourcePos) RuntimeTypeInfo
empty = M.empty


-- |Combines two environments, ensuring that the runtime types of identifers
-- at the same position are identical.
unionEnv :: Env -> Env -> M Env
unionEnv env1 env2 = foldM f env1 (M.toList env2)
  where f :: Env -> ((Id, SourcePos), RuntimeTypeInfo) -> M Env
        f env (x, t) = case M.lookup x env of
          Nothing -> return (M.insert x t env)
          -- Just t' -> case t == t' of
          --   True -> return env
          --   False -> catastrophe noPos "%s has distinct types %s and %s"
          --     (show x) (show t) (show t')
          Just TUnreachable -> return (M.insert x t env)
          Just TUnk -> return env -- necessary for DoWhileStmt
          Just t' -> case t of
            TUnreachable -> return env
            TUnk -> return (M.insert x TUnk env)
            otherwise -> case t == t' of
              True -> return env
              False -> fail $ printf 
                "RuntimeAnnotations.hs : %s has distinct types %s and %s"
                (show x) (show t) (show t')


unionEnvs = foldM unionEnv M.empty

expr :: Map Id RuntimeTypeInfo
     -- ^result of @localTypes@
     -> Expr (Node, SourcePos)
     -- ^annotated result from intraprocedural graph
     -> M Env
expr env e = case e of
  Lit _ -> return empty
  VarRef _ "this" -> return empty
  VarRef (_, p) x -> case M.lookup x env of
    Just rt -> return (M.singleton (x, p) rt)
    Nothing -> catastrophe p $
      printf "RuntimeAnnotations.hs : %s does not have a runtime type \
             \annotation in a VarRef." x
  DotRef (_, p) e _ -> expr env e
  BracketRef (_, p) e1 e2 -> do
    r1 <- expr env e1
    r2 <- expr env e2
    unionEnv r1 r2
  OpExpr _ _ es -> do
    rs <- mapM (expr env) es
    unionEnvs rs


lookupEnv :: Map Node (Map Id RuntimeTypeInfo)
          -> Node
          -> M (Map Id RuntimeTypeInfo)
lookupEnv envs node = case M.lookup node envs of
  Just env -> return env
  Nothing -> fail "CATASTROPHIC FAILURE: RuntimeAnnotations.hs : environment \
                  \not found for node %s" (show node)


stmt :: Map Node (Map Id RuntimeTypeInfo) 
        -- ^result of @localTypes@
        -> Stmt (Node, SourcePos) 
        -- ^annotated result from intraprocedural graph
        -> M Env
stmt envs s = case s of
  SeqStmt _ ss -> do
    rs <- mapM (stmt envs) ss
    unionEnvs rs
  EmptyStmt _ -> return empty
  AssignStmt (node, p) x e -> do
    env <- lookupEnv envs node
    r <- expr env e
    case M.lookup x env of
      Just rt -> unionEnv r (M.singleton (x, p) rt)
      Nothing -> return r -- x is not refined
  DirectPropAssignStmt (node, p) _ _ e -> do
    env <- lookupEnv envs node
    expr env e
  IndirectPropAssignStmt (node, p) _ _ e -> do
    env <- lookupEnv envs node
    expr env e
  DeleteStmt (node, p) obj field -> return empty
  NewStmt (node, p) result constr args -> return empty
  CallStmt (node, p) result func args -> return empty
  IfStmt (node, _) e s1 s2 -> do
    env <- lookupEnv envs node
    r1 <- expr env e
    r2 <- stmt envs s1
    r3 <- stmt envs s2
    unionEnvs [r1, r2, r3]
  WhileStmt (node, _) e s' -> do
    env <- lookupEnv envs node
    r1 <- expr env e
    r2 <- stmt envs s'
    unionEnv r1 r2
  ForInStmt  (node, _) x e s' -> do
    env <- lookupEnv envs node
    r1 <- expr env e
    r2 <- stmt envs s'
    unionEnv r1 r2
  TryStmt _ s1 x s2 s3 -> do
    r1 <- stmt envs s1
    r2 <- stmt envs s2
    r3 <- stmt envs s3
    unionEnvs [r1, r2, r3]
  ThrowStmt (node, _) e' -> do
    env <- lookupEnv envs node
    expr env e'
  ReturnStmt _ Nothing -> return empty
  ReturnStmt (node, _) (Just e') -> do
    env <- lookupEnv envs node
    expr env e'
  LabelledStmt _ _ s' ->
    stmt envs s'
  BreakStmt _ _ ->
    return empty
  ContinueStmt _ _ -> 
    return empty
  SwitchStmt _ _ cases default_ -> do
    rs <- mapM (stmt envs) (default_:(map snd cases))
    unionEnvs rs
  EnterStmt _ ->
    return empty
  ExitStmt _ ->
    return empty


annotateVarRef :: Env 
               -> Stx.Expression SourcePos 
               -> Stx.Expression SourcePos
annotateVarRef env (Stx.VarRef p (Stx.Id p' x)) = case M.lookup (x, p) env of
  Just (TKnown rt) -> Stx.AnnotatedVarRef p rt x
  otherwise -> Stx.VarRef p (Stx.Id p' x)
annotateVarRef _ e = e


removeFunction :: Stx.Expression SourcePos -> Stx.Expression SourcePos
removeFunction (Stx.FuncExpr p args t body) = 
  Stx.FuncExpr p [] t (Stx.EmptyStmt p)
removeFunction e = e


isFunction :: Stx.Expression SourcePos -> Bool
isFunction (Stx.FuncExpr {}) = True
isFunction e = False


topLevelRuntimeAnnotations :: Map Id RuntimeTypeInfo
                           -- ^types of formal arguments and identifiers in the 
                           -- enclosing environment
                           -> [Stx.TopLevel SourcePos]
                           -> Either String [Stx.TopLevel SourcePos]
                           -- ^body with @VarRef@s transformed to 
                           -- @AnnotatedVarRef@s
                           -- where possible.
topLevelRuntimeAnnotations env body = do
  let body' = everywhere' (mkT removeFunction) body -- efficiency only
  (vars, anf) <- toANF (map eraseTypesTopLevel  body')
  let wrapped = SeqStmt noPos ((EnterStmt noPos) : (anf ++ [ExitStmt noPos]))
  let (anf', _) = numberStmts 0 wrapped
  let vars' = map (\(x,p) -> (x, (0, p))) vars
  let (_, _, gr) = intraproc (FuncLit (0, noPos) [] vars' anf')
  let localEnv = M.fromList (map (\(x, _) -> (x, TUnreachable)) vars)
  let stmtEnvs = localTypes gr (M.union localEnv env)
  case runIdentity (runErrorT $ stmt stmtEnvs anf') of
    Left err -> Left err
    Right localEnv -> Right $
      everywhereBut (mkQ False isFunction) 
                    (mkT (annotateVarRef localEnv)) 
                    body




runtimeAnnotations :: MonadError String m
                   => Map Id RuntimeTypeInfo
                   -- ^types of formal arguments and identifiers in the 
                   -- enclosing environment
                   -> Map Id Type -- ^declared types of local variables
                   -> Stx.Statement SourcePos
                   -- ^body of a function / top level
                   -> m (Stx.Statement SourcePos)
                   -- ^body with @VarRef@s transformed to @AnnotatedVarRef@s
                   -- where possible.
runtimeAnnotations env locals body = do
  let body' = everywhere' (mkT removeFunction) body
  case toANF (eraseTypes [body']) of
    Left err -> fail err
    Right (vars, anf) -> do
      let wrapped = SeqStmt noPos ((EnterStmt noPos):(anf ++ [ExitStmt noPos]))
      let (anf', _) = numberStmts 0 wrapped
      let vars' = map (\(x,p) -> (x, (0, p))) vars
      let (_, _, gr) = intraproc (FuncLit (0, noPos) [] vars' anf')
      let localEnv =
            (M.map runtime locals) `M.union`
            (M.fromList (map (\(x, _) -> (x, TUnreachable)) vars))
      let stmtEnvs = localTypes gr (M.union localEnv env)
      case runIdentity (runErrorT $ stmt stmtEnvs anf') of
        Left err -> fail err
        Right localEnv -> return $
          everywhereBut (mkQ False isFunction) 
                        (mkT (annotateVarRef localEnv)) 
                        body
