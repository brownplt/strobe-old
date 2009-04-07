module TypedJavaScript.TypeCheck  where

import TypedJavaScript.Prelude
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Graph.Inductive as G
import Control.Monad.State.Strict
import qualified TypedJavaScript.Syntax as TJS
import TypedJavaScript.Syntax (Type (..), VP (..))
import TypedJavaScript.Environment
import TypedJavaScript.Types
import TypedJavaScript.Graph
import BrownPLT.JavaScript.Analysis (jsToCore, simplify)
import BrownPLT.JavaScript.Analysis.Intraprocedural (Graph,
  allIntraproceduralGraphs)
import BrownPLT.JavaScript.Analysis.ANF
import BrownPLT.JavaScript.Analysis.ANFUtils
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

  mapM_ (stmtForBody env ee rettype) nodes

  finalLocalEnv <- lookupLocalEnv (exitNodeOf gr)
  return finalLocalEnv
  -- TODO: account for removedEdges

stmtForBody :: Env -- ^environment of the enclosing function for a nested
                   -- function, or the globals for a top-level statement or
                   -- function
            -> ErasedEnv
            -> Type SourcePos
            -> G.Node
            -> TypeCheck ()
stmtForBody enclosingEnv erasedEnv rettype node = do
  localEnv <- lookupLocalEnv node
  s <- nodeToStmt node
  succs <- stmt (M.union localEnv enclosingEnv) erasedEnv rettype node s
  mapM_ updateLocalEnv succs
    
stmtSuccs :: G.Node -> TypeCheck [G.Node]
stmtSuccs stmtNode = do
  state <- get
  return (G.suc (stateGraph state) stmtNode)

subtypeError :: Monad m
             => SourcePos
             -> Type SourcePos -- ^expected
             -> Type SourcePos -- ^received
             -> m a
subtypeError loc expected received =
  fail $ printf "at %s: expected subtype of %s, received %s" (show loc)
                (show expected) (show received)

typeError :: Monad m
          => SourcePos
          -> String
          -> m a
typeError loc msg = fail $ printf "at %s: %s" (show loc) msg

catastrophe :: Monad m
            => SourcePos
            -> String
            -> m a
catastrophe loc msg =
  fail $ printf "CATASTROPHIC FAILURE: %s (at %s)" msg (show loc)

forceEnvLookup :: Monad m
               => SourcePos -> Env -> Id -> m (Type SourcePos)
forceEnvLookup loc env name = case M.lookup name env of
  Nothing -> 
    fail $ printf "at %s: identifier %s is unbound" (show loc) name
  Just Nothing -> 
    fail $ printf "at %s: identifier %s is unbound" (show loc) name
  Just (Just t) -> return t

assertSubtype :: Monad m
              => SourcePos -> Type SourcePos -> Type SourcePos -> m ()
assertSubtype loc received expected = case received <: expected of
  True -> return ()
  False -> subtypeError loc expected received


stmt :: Env -- ^the environment in which to type-check this statement
     -> ErasedEnv
     -> Type SourcePos
     -> G.Node -- ^the node representing this statement in the graph
     -> Stmt (Int, SourcePos)
     -> TypeCheck [(G.Node, Env)]
stmt env ee rettype node s = do
  succs <- stmtSuccs node
  -- statements that do not affect the incoming environment are "no-ops"
  let noop = return (zip succs (repeat env))
  case s of
    EnterStmt _ -> noop
    ExitStmt _ -> noop
    SeqStmt{} -> noop
    EmptyStmt _ -> noop
    AssignStmt (_,p) v e -> do
      (te,v_vp) <- expr env ee e
      case M.lookup v env of
        Nothing -> 
          fail $ printf "at %s: identifier %s is unbound" (show p) v
        Just Nothing -> do
          let env' = M.insert v (Just te) env
          return $ zip succs (repeat env')
        Just (Just t) | te <: t -> noop
                      | otherwise -> subtypeError p t te
    DirectPropAssignStmt _ obj method e -> undefined
    IndirectPropAssignStmt _ obj method e -> fail "obj[method] NYI"
    DeleteStmt _ r del -> fail "delete NYI"
    NewStmt{} -> fail "NewStmt will be removed from ANF"
    CallStmt (_,p) r_v f_v args_v -> do
        f <- forceEnvLookup p env f_v
        actuals' <- mapM (forceEnvLookup p env) args_v
        let actuals = tail (tail actuals') -- drop this, arguments for now
        case deconstrFnType f of
          Nothing -> typeError p ("expected function; received " ++ show f)
          Just ([], [], formals, r, latentPred) -> do
            let (supplied, missing) = splitAt (length actuals) formals
            unless (length formals >= length actuals) $ do
              typeError p (printf "function expects %d arguments, but %d \
                                  \were supplied" (length formals)
                                  (length actuals))
            let checkArg (actual,formal) = do
                  unless (actual <: formal) $
                    subtypeError p formal actual
            mapM_ checkArg (zip actuals supplied)
            let checkMissingArg actual = do
                  unless (undefType <: actual) $
                    typeError p "non-null argument not supplied"
            mapM_ checkMissingArg missing
            -- For call statemens, we must ensure that the result type is
            -- a subtype of the named result.
            case M.lookup r_v env of
              Nothing -> catastrophe p (printf "result %s is unbound" r_v)
              Just Nothing -> do
                let env' = M.insert r_v (Just r) env
                return $ zip succs (repeat env')
              Just (Just r') | r <: r' -> noop -- No refinement?
                             | otherwise -> subtypeError p r' r
   {- 
            --if we have a 1-arg func that has a latent pred, applied to a
            --visible pred of VID, then this is a T-AppPred        
            let isvpid (VPId _) = True
                isvpid _        = False
                a1vp            = args_vp !! 0
            if length formals_t == 1 
               && latentPred /= LPNone && isvpid a1vp
              then let (VPId id) = a1vp
                       (LPType ltype) = latentPred
                    in return (result_t, VPType ltype id) -}
          Just (typeArgs,_,_,_,_) ->
            -- This should not happen:
            -- forall a b c. forall x y z . int -> bool
            catastrophe p "application still has uninstantiated type variables"
         
    IfStmt _ e s1 s2 -> do
      t <- expr env ee e -- this permits non-boolean tests
      noop -- will change for occurrence types
    WhileStmt _ e s -> do
      expr env ee e -- this permits non-boolean tests
      noop -- Will change for occurrence types
    ForInStmt _ id e s -> fail "ForIn NYI"
    TryStmt _ s id catches finally  -> fail "TryStmt NYI"
    ThrowStmt _ e -> do
      expr env ee e
      noop
    ReturnStmt (_,p) Nothing 
      | undefType <: rettype -> noop
      | otherwise -> subtypeError p rettype undefType
    ReturnStmt (_,p) (Just e) -> do
      (te, vp) <- expr env ee e
      if te <: rettype
        then noop
        else subtypeError p rettype te
    LabelledStmt _ _ _ -> noop
    BreakStmt _ _ -> noop
    ContinueStmt _ _ -> noop
    SwitchStmt _ _ cases default_ -> undefined

expr :: Env -- ^the environment in which to type-check this expression
     -> ErasedEnv
     -> Expr (Int,SourcePos)
     -> TypeCheck (Type SourcePos, VP) 
expr env ee e = case e of 
  VarRef (_,p) id -> do
    t <- forceEnvLookup p env id
    return (t,VPId id)
  DotRef{} -> fail "NYI"
  BracketRef{} -> fail "NYI"
  OpExpr (_,p) f args_e -> do
    args <- mapM (expr env ee) args_e
    t <- operator p f (map fst args)
    return (t, VPNone)
  Lit (StringLit (_,a) s) -> 
    return (TId a "string", if length s == 0 then VPFalse else VPTrue)
  Lit (RegexpLit _ _ _ _) -> fail "regexp NYI"
  Lit (NumLit (_,p) n) ->
    return (TId p "double", if n == 0 then VPFalse else VPTrue)
  Lit (IntLit (_,a) n) -> 
    return (TId a "int", if n == 0 then VPFalse else VPTrue)
  Lit (BoolLit (_,p) v) ->
    return (TId p "bool", if v then VPTrue else VPFalse)
  Lit (NullLit (_,p)) -> fail "NullLit NYI (not even in earlier work)"
  Lit (ArrayLit (_,p) es) -> do
    -- TODO: Allow subtyping
    r <- mapM (expr env ee) es
    let ts = map fst r
    if (length (nub ts) == 1) 
      then return (TApp p (TId p "Array") [head ts], VPTrue)
      else fail "array subtyping NYI"
  Lit (ObjectLit _ props) -> fail "object lits NYI"
  Lit (FuncLit (_, p) args locals body) -> case M.lookup p ee of
    Nothing -> catastrophe p "function type is not in the erased environment"
    Just [t] -> return (t, VPTrue)
    Just _ -> catastrophe p "many types for function in the erased environment"
  
operator :: SourcePos -> FOp 
         -> [Type SourcePos] -> TypeCheck (Type SourcePos)
operator loc op args = do
  -- The ANF transform gaurantees that the number of arguments is correct for
  -- the specified operator.
  let lhs = args !! 0
  let rhs = args !! 1 -- Do not use rhs if  op takes just one argument!
  let cmp = do
        unless ((lhs == stringType && rhs == stringType) ||
                (lhs <: doubleType && rhs <: doubleType)) $ do
          typeError loc (printf "can only compare numbers and strings")
        return boolType
  let bool = if lhs == rhs && lhs == boolType
               then return boolType
               else typeError loc "expected a boolean"
  let numeric requireInts returnDouble = do
        assertSubtype loc lhs
          (if requireInts then intType else doubleType)
        assertSubtype loc rhs
          (if requireInts then intType else doubleType)
        if returnDouble
          then return doubleType
          else return (if lhs <: intType then rhs else lhs)
  case op of
    OpLT -> cmp
    OpLEq -> cmp
    OpGT -> cmp
    OpGEq -> cmp 
    OpIn -> fail "OpIn NYI"
    OpInstanceof -> fail "OpInstanceof NYI"
    OpEq -> return boolType
    OpStrictEq -> return boolType
    OpNEq -> return boolType
    OpStrictNEq -> return boolType
    OpLAnd -> bool
    OpLOr -> bool
    OpMul -> numeric False False
    OpDiv -> numeric False True
    OpMod -> numeric False True
    OpSub -> numeric False False
    OpLShift -> numeric True False
    OpSpRShift -> numeric True False
    OpZfRShift -> numeric True False
    OpBAnd -> numeric True False
    OpBXor -> numeric True False
    OpBOr -> numeric True False
    OpAdd | lhs == rhs && lhs == stringType -> return stringType
          | otherwise -> numeric False False
    PrefixLNot -> do
      assertSubtype loc lhs boolType
      return boolType
    PrefixBNot -> do
      assertSubtype loc lhs intType
      return intType
    PrefixMinus -> do
      assertSubtype loc lhs doubleType
      return lhs
    PrefixVoid -> do
      catastrophe loc (printf "void has been removed")
    PrefixTypeof -> do
      fail "typeof NYI"


-- |When a node has multiple parents, this function combines their environments.
unionEnv :: Env -> Env -> Env
unionEnv env1 env2 =
  foldl' (\env (id, maybeType) -> M.insertWith unionType id maybeType env)
         env1 (M.toList env2)

uneraseEnv :: Env -> ErasedEnv -> Lit (Int, SourcePos) -> (Env, Type SourcePos)
uneraseEnv env ee (FuncLit (_, pos) args locals _) = (env', rettype) where
  functype = head $ ee ! pos
  Just (_, cs, types, rettype, lp) = deconstrFnType functype
  -- undefined for this, arguments
  args' = args -- if null args then args else (tail $ tail args)
  argtypes = zip (map fst args') (map Just (undefined:undefined:types))
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
  let globalEnv = M.fromList [("this", Just (TObject noPos []))]
  (env, state) <- runStateT (typeCheckProgram globalEnv (envs, intraprocs)) 
                            (TypeCheckState G.empty M.empty)
  return env

