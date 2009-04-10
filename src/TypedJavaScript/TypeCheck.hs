module TypedJavaScript.TypeCheck  where

import TypedJavaScript.Prelude
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Graph.Inductive as G
import Control.Monad.State.Strict
import qualified TypedJavaScript.Syntax as TJS
import TypedJavaScript.Syntax (Type (..), VP (..), LatentPred (..))
import TypedJavaScript.Environment
import TypedJavaScript.Types
import TypedJavaScript.Graph
import BrownPLT.JavaScript.Analysis (jsToCore, simplify)
import BrownPLT.JavaScript.Analysis.Intraprocedural (Graph,
  allIntraproceduralGraphs)
import BrownPLT.JavaScript.Analysis.ANF
import BrownPLT.JavaScript.Analysis.ANFUtils
import BrownPLT.JavaScript.Analysis.ANFPrettyPrint
import TypedJavaScript.ErasedEnvTree
import TypedJavaScript.TypeErasure

import Paths_TypedJavaScript
import Text.ParserCombinators.Parsec
import TypedJavaScript.Parser (parseToplevels)

import System.Directory
import System.FilePath

data TypeCheckState = TypeCheckState {
  stateGraph :: Graph,
  stateEnvs :: Map Int Env
}


type TypeCheck a = StateT TypeCheckState IO a

-- |Returns the successors of the node, paired with the labels on the
-- |edges to the successors.
stmtSuccs :: Stmt (Int, SourcePos) -> 
             TypeCheck [(G.Node, Maybe (Lit (Int, SourcePos)))]
stmtSuccs s = do
  state <- get
  let node = fst (stmtLabel s)
  let gr = stateGraph state
  return (G.lsuc gr node) 


nodeToStmt :: G.Node -> TypeCheck (Stmt (Int,SourcePos))
nodeToStmt node = do
  state <- get
  -- Nodes are just integers, so looking up the
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
               => SourcePos -> Env -> Id -> m (Type SourcePos, Maybe VP)
forceEnvLookup loc env name = case M.lookup name env of
  Nothing -> 
    fail $ printf "at %s: identifier %s is unbound" (show loc) name
  Just Nothing -> 
    fail $ printf "at %s: identifier %s is unbound" (show loc) name
  Just (Just t) -> return t

assert :: Monad m => Bool -> String -> m ()
assert True _ = return ()
assert False msg = fail ("CATASPROPHIC FAILURE: " ++  msg)

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
  succs <- stmtSuccs s
  -- statements that do not affect the incoming environment are "no-ops"
  let noop = return (zip (map fst succs) (repeat env))
  case s of
    EnterStmt _ -> noop
    ExitStmt _ -> noop
    SeqStmt{} -> noop
    EmptyStmt _ -> noop
    AssignStmt (_,p) v e -> do
      (te,e_vp) <- expr env ee e
      case M.lookup v env of        
        Nothing -> --unbound id
          fail $ printf "at %s: identifier %s is unbound" (show p) v
        Just Nothing -> do --ANF variable, or locally inferred variable
          let env' = if v !! 0 == '@'
                       then M.insert v (Just (te, Just e_vp)) env
                       else M.insert v (Just (te, Nothing)) env
          return $ zip (map fst succs) (repeat env')
        Just (Just (t, v_vp)) --explicitly typed variable, or ANF w/ type now
          --the presence of these asserts makes me think our env-type is
          --not descriptive enough.
          | v !! 0 == '@' -> fail $ printf "var at %s has type %s" (show p)
                                    (show t)

          | v_vp /= Nothing -> fail "non-ANF var shouldn't have a VP"
          | te <: t -> noop 
          | otherwise -> subtypeError p t te
    DirectPropAssignStmt _ obj method e -> undefined
    IndirectPropAssignStmt _ obj method e -> fail "obj[method] NYI"
    DeleteStmt _ r del -> fail "delete NYI"
    NewStmt{} -> fail "NewStmt will be removed from ANF"
    CallStmt (_,p) r_v f_v args_v -> do
        (f, f_vp) <- forceEnvLookup p env f_v
        actualsWithVP' <- mapM (forceEnvLookup p env) args_v
        let (actuals', actuals_mvps) = unzip actualsWithVP'
        --actuals_vps contains Maybe VP. If it's Just, then it's an ANF
        --var remembering its VP. If it's Nothing, then it's a real variable,
        --and it's VP is the variable itself.
        let getvp name mvp = case mvp of
              Nothing -> VPId name
              Just vp  
                | name !! 0 /= '@' -> error "non-ANF var has VP in the env"
                | otherwise        -> vp
            actuals_vps = zipWith getvp args_v actuals_mvps
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
    
            --if we have a 1-arg func that has a latent pred, applied to a
            --visible pred of VID, then this is a T-AppPred        
            let isvpid (VPId _) = True
                isvpid _        = False
                arg1_vp         = actuals_vps !! 0
                r_vp = if length formals == 1 
                          && latentPred /= LPNone && isvpid arg1_vp
                         then let (VPId id) = arg1_vp
                                  (LPType ltype) = latentPred
                               in (VPType ltype id)
                         else VPNone
                
            -- For call statemens, we must ensure that the result type is
            -- a subtype of the named result.
            case M.lookup r_v env of
              Nothing -> catastrophe p (printf "result %s is unbound" r_v)
              Just Nothing -> do --ANF, or type-infer
                let env' = if r_v !! 0 == '@'
                             then M.insert r_v (Just (r, Just r_vp)) env
                             else M.insert r_v (Just (r, Nothing)) env
                return $ zip (map fst succs) (repeat env')
              Just (Just (r', r_vp) )
                | r_v !! 0 == '@' -> fail "ANF var has type"
                | r_vp /= Nothing -> fail "non-ANF var shouldn't have a VP"
                | r <: r' -> noop -- No refinement?
                | otherwise -> subtypeError p r' r
 
          Just (typeArgs,_,_,_,_) ->
            -- This should not happen:
            -- forall a b c. forall x y z . int -> bool
            catastrophe p "application still has uninstantiated type variables"
         
    IfStmt (_, p) e s1 s2 -> do
      (t, vp) <- expr env ee e -- this permits non-boolean tests
      assertSubtype p t boolType
      assert (length succs == 2) "IfStmt should have two successors"
      
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
    (t, mvp) <- forceEnvLookup p env id
    case mvp of
      Nothing | id !! 0 == '@' -> fail "ANF var should have VP"
              | otherwise      -> return (t, VPId id)
      Just vp | id !! 0 /= '@' -> fail "non-ANf var shouldn't have VP"
              | otherwise      -> return (t, vp) 
  DotRef{} -> fail "NYI"
  BracketRef{} -> fail "NYI"
  OpExpr (_,p) f args_e -> do
    args <- mapM (expr env ee) args_e
    operator p f args
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
    Just [t] -> case deconstrFnType t of
      Just (_, _, argTypes, _, _) 
        | length argTypes == (length args - 2) -> return (t, VPTrue)
        | otherwise -> typeError p "invalid number of arguments"
      Nothing -> typeError p "not a function type"
    Just _ -> catastrophe p "many types for function in the erased environment"
  
operator :: SourcePos -> FOp 
         -> [(Type SourcePos, VP)] -> TypeCheck (Type SourcePos, VP)
operator loc op argsvp = do
  let (args, vps) = unzip argsvp
  -- The ANF transform gaurantees that the number of arguments is correct for
  -- the specified operator.
  let novp t = (t, VPNone)
  
  let lhs = args !! 0
  let rhs = args !! 1 -- Do not use rhs if op takes just one argument!
  let lvp = vps !! 0
      rvp = vps !! 1                      
  let cmp = do
        unless ((lhs == stringType && rhs == stringType) ||
                (lhs <: doubleType && rhs <: doubleType)) $ do
          typeError loc (printf "can only compare numbers and strings")
        return $ novp boolType
  let bool = if lhs == rhs && lhs == boolType
               then return $ novp boolType
               else typeError loc "expected a boolean"
  let numeric requireInts returnDouble = do
        assertSubtype loc lhs
          (if requireInts then intType else doubleType)
        assertSubtype loc rhs
          (if requireInts then intType else doubleType)
        if returnDouble
          then return $ novp doubleType
          else return $ novp (if lhs <: intType then rhs else lhs)

  --TODO: equalityvp will only work once we have value types again
  let equalityvp a b@(_,VPTypeof _) = equalityvp b a
      equalityvp (_,(VPTypeof i)) (TVal (StringLit _ s) (TId p "string"),_) =
        case s of
          "number" -> VPType (TId p "double") i
          "undefined" -> VPType undefType i
          "boolean" -> VPType (TId p "bool") i
          "string" -> VPType (TId p "string") i
          "function" -> error "vp for typeof x == 'function' nyi"
          "object" -> error "vp for typeof x == 'object' nyi"
          _ -> VPNone
      equalityvp _ _ = VPNone

  case op of
    OpLT -> cmp
    OpLEq -> cmp
    OpGT -> cmp
    OpGEq -> cmp 
    OpIn -> fail "OpIn NYI"
    OpInstanceof -> fail "OpInstanceof NYI"

    OpEq        -> return (boolType, equalityvp (lhs,lvp) (rhs,rvp))
    OpStrictEq  -> return (boolType, equalityvp (lhs,lvp) (rhs,rvp))
    OpNEq       -> return (boolType, 
                           VPNot (equalityvp (lhs,lvp) (rhs,rvp)))
    OpStrictNEq -> return (boolType, 
                           VPNot (equalityvp (lhs,lvp) (rhs,rvp)))

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
    OpAdd | lhs == stringType || rhs == stringType -> return $ novp stringType
          | otherwise -> numeric False False
    PrefixLNot -> do
      assertSubtype loc lhs boolType
      return $ novp boolType
    PrefixBNot -> do
      assertSubtype loc lhs intType
      return $ novp intType
    PrefixMinus -> do
      assertSubtype loc lhs doubleType -- TODO: more like, asserSub intType
      return $ novp lhs
    PrefixVoid -> do
      catastrophe loc (printf "void has been removed")
    PrefixTypeof -> case lvp of 
      VPId i -> return (stringType, VPTypeof i)
      _      -> return (stringType, VPNone)


-- |When a node has multiple parents, this function combines their environments.
unionEnv :: Env -> Env -> Env
unionEnv env1 env2 =
  foldl' (\env (id, maybeType) -> M.insertWith unionTypeVP id maybeType env)
         env1 (M.toList env2)

uneraseEnv :: Env -> ErasedEnv -> Lit (Int, SourcePos) -> (Env, Type SourcePos)
uneraseEnv env ee (FuncLit (_, pos) args locals _) = (env', rettype) where
  lookupEE pos name = case M.lookup pos ee of
    Nothing -> Nothing
    Just t | head name == '@' -> Nothing
           | otherwise -> Just t
  functype = head $ ee ! pos
  Just (_, cs, types, rettype, lp) = deconstrFnType functype
  -- undefined for this, arguments
  args' = args -- if null args then args else (tail $ tail args)
  argtypes = zip (map fst args') (map Just (undefined:undefined:types))
  localtypes = map (\(name,(_, pos)) -> (name, liftM head (lookupEE pos name))) 
                   locals
  --the only typed things here are args and explicitly typed locals, neither
  --of which have VPs.
  novp (a,Just t)  = (a, Just (t, Nothing))
  novp (a,Nothing) = (a, Nothing)
  env' = M.union (M.fromList (map novp $ argtypes++localtypes)) env 
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
  liftIO $ putStrLn $ "\n" ++ (prettyANF anfProg)
  let (anf, intraprocs) = allIntraproceduralGraphs (topDecls, anfProg)
  -- Since all type annotations are erased in the previous step, map locations
  -- to type annotations, so they may be recovered later.  The locations are
  -- that of identifiers that had type annotations, functions that had type
  -- annotations, object fields that had type annotations.
  --
  -- These "erased environments" are returned in a tree with the same shape as
  -- 'intraprocs' above.
  let envs = buildErasedEnvTree prog
  
  -- load the global environment from "core.js"
  dir <- getDataDir
  toplevels' <- parseFromFile (parseToplevels) (dir </> "core.tjs")
  toplevels <- case toplevels' of
    Left err -> fail $ "PARSD ERROR ON CORE.TJS: " ++ show err
    Right tls -> return tls
  
  -- (varenv, typeenv)
  let tl2env (TJS.ExternalStmt _ (TJS.Id _ s) t) = 
        (M.singleton s (Just (t, Nothing)), M.empty)
      tl2env (TJS.TypeStmt _ (TJS.Id _ s) t) =  
        (M.empty, M.singleton s (Just (t, Nothing)))

  --TODO: pass typeenv around, too.
  let globalVarEnv = M.unions $ 
        (map fst (map tl2env toplevels)) ++ 
        [M.fromList [("this", Just (TObject noPos [], Nothing))]]
  
  (env, state) <- runStateT (typeCheckProgram globalVarEnv (envs, intraprocs)) 
                            (TypeCheckState G.empty M.empty)
  return env

