module TypedJavaScript.TypeCheck where

import TypedJavaScript.Prelude
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Graph.Inductive as G
import Control.Monad.State.Strict
import qualified TypedJavaScript.Syntax as TJS
import TypedJavaScript.Syntax (Type (..), VP (..), LatentPred (..))
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
  stateEnvs :: Map Int Env,
  typeEnv :: Map String (Type SourcePos)
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

assertReturn :: Monad m => SourcePos -> Maybe (Stmt (Int, SourcePos)) -> m ()
assertReturn loc Nothing = 
  catastrophe loc "predecessor of an Exit node is unlabelled in the control \
                  \flow graph"
assertReturn _ (Just (ReturnStmt _ _)) =
  return ()
assertReturn loc (Just s) =
  typeError (snd $ stmtLabel s) "expected return after this statement"


body :: Env
     -> ErasedEnv
     -> Type SourcePos
     -> G.Node
     -> G.Node
     -> TypeCheck Env
body env ee rettype enterNode exitNode = do
  state <- get
  let gr = stateGraph state
  -- Enter has no predecessors
  unless (null $ G.pre gr enterNode) $
    fail $ "Unexpected edges into  " ++ show (G.lab gr enterNode)
  -- All predecessors of Exit must be ReturnStmt
  exitStmt <- nodeToStmt exitNode
  let exitPos = snd (stmtLabel exitStmt)
  mapM_ (assertReturn exitPos) (map (G.lab gr) (G.pre gr exitNode))

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
             => SourcePos -> String
             -> Type SourcePos -- ^expected
             -> Type SourcePos -- ^received
             -> m a
subtypeError loc func expected received =
  fail $ printf "%s: at %s: expected subtype of %s, received %s" 
                (show func) (show loc)
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
               => SourcePos -> Env -> Id -> m (Type SourcePos, VP)
forceEnvLookup loc env name = case M.lookup name env of
  Nothing -> 
    fail $ printf "at %s: identifier %s is unbound" (show loc) name
  Just Nothing -> 
    fail $ printf "at %s: identifier %s is unbound" (show loc) name
  Just (Just t) -> return t

assert :: Monad m => Bool -> String -> m ()
assert True _ = return ()
assert False msg = fail ("CATASPROPHIC FAILURE: " ++  msg)

assertSubtype :: MonadIO m
              => SourcePos -> String -> Type SourcePos -> Type SourcePos -> m ()
assertSubtype loc name received expected = case received <: expected of
  True -> return ()
  False -> do
    --liftIO $ putStrLn $ printf "%s == %s: %s" (show received) (show expected)
    --                     (show (received == expected))
    --liftIO $ putStrLn $ printf "%s <: %s: %s" (show received) (show expected)
    --                     (show (received <: expected))
    subtypeError loc name expected received

stmt :: Env -- ^the environment in which to type-check this statement
     -> ErasedEnv
     -> Type SourcePos
     -> G.Node -- ^the node representing this statement in the graph
     -> Stmt (Int, SourcePos)
     -> TypeCheck [(G.Node, Env)]
stmt env ee rettype node s = do
  state <- get
  let tenv = typeEnv state
  succs <- stmtSuccs s
  -- statements that do not affect the incoming environment are "no-ops"
  let noop = return (zip (map fst succs) (repeat env))
  case s of
    EnterStmt _ -> noop
    ExitStmt _ -> noop
    SeqStmt{} -> noop
    EmptyStmt _ -> noop
    AssignStmt (_,p) v e -> do
      --TODO: distinguish TRefined from Type.
      --TODO: make this do a gammaPlus instead of all this.
      (te,e_vp) <- expr env ee e
      case M.lookup v env of        
        Nothing -> --unbound id
          fail $ printf "at %s: identifier %s is unbound" (show p) v
        Just Nothing -> do --ANF variable, or locally inferred variable
          let env' = M.insert v (Just (te, 
                                       VPMulti [VPId v, e_vp])) env
          return $ zip (map fst succs) (repeat env')
        Just (Just (TRefined t _, vp)) | te <: t -> do
          -- If the LHS has been refined, we can "revert" to its declared
          -- type.
          let env' = M.insert v (Just ((TRefined t te), VPMulti [VPId v, vp]))
                              env
          return $ zip (map fst succs) (repeat env')
        Just (Just (t, v_vp)) -> do
          assertSubtype p "AssignStmt" te t
          -- TODO: remove, from environment, any VP referring to this var!
          let env' = M.insert v (Just (TRefined t te, VPMulti [VPId v, v_vp])) 
                              env
          return $ zip (map fst succs) (repeat env')              
    DirectPropAssignStmt (_,p) obj prop e -> do
      (t_rhs, e_vp) <- expr env ee e
      case M.lookup obj env of
        Nothing -> 
          catastrophe p (printf "id %s for an object is unbound" obj)
        Just Nothing -> do
          -- Variable is in scope but is yet to be defined.
          fail $ printf "at %s: can't assign to obj %s; has no type yet"
                   (show p) obj
        Just (Just (t, vp)) -> case unRec (refined t) of
          TObject _ props -> case lookup prop props of
            Nothing -> 
              typeError p (printf "object does not have the property %s" prop)
            Just t' -> do
              assertSubtype p "DirectPropAssignStmt" t_rhs t'
              noop -- TODO: Affect the VP somehow?
          t' -> typeError p (printf "expected object, received %s" (show t'))
    IndirectPropAssignStmt _ obj method e -> fail "obj[method] NYI"
    DeleteStmt _ r del -> fail "delete NYI"
    NewStmt{} -> fail "NewStmt will be removed from ANF"
    CallStmt (_,p) r_v f_v args_v -> do
        (f'', f_vp) <- forceEnvLookup p env f_v
        let f' = refined f''
        f <- case f' of
               TForall{} -> do
                 case M.lookup p ee of 
                   Nothing -> fail $ printf "at %s: callstmt not in ee"
                                       (show p)
                   Just apps -> applyType p f' apps
               _ -> return f'
        actualsWithVP' <- mapM (forceEnvLookup p env) args_v
        let (this':arguments:actuals', actuals_vps) = unzip actualsWithVP'
        this <- dotrefContext this' --motivation: if 'this' is a
                                    --string, int, etc, it is automatically
                                    --converted to an object.
         
        --actuals_vps contains VP, including VPId for the var name itself.
        let actuals = this:actuals'
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
                    subtypeError p "CallStmt" formal actual
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
                
            -- For call statements, we must ensure that the result type is
            -- a subtype of the named result.
            case M.lookup r_v env of
              Nothing -> catastrophe p (printf "result %s is unbound" r_v)
              Just Nothing -> do --ANF, or type-infer
                let env' = M.insert r_v (Just (r, r_vp)) env
                --TODO: also modify env based on what vars the
                --function modifies that aren't local to that function
                --itself.
                return $ zip (map fst succs) (repeat env')
              Just (Just (TRefined r_vt _, vp))
                | r <: r_vt -> do
                    let env' = M.insert r_v (Just (TRefined r_vt r,
                                                   VPMulti [VPId r_v, r_vp]))
                                            env
                    return $ zip (map fst succs) (repeat env')
              Just (Just (r_vt, r_vp)) 
                | r <: r_vt -> do
                    let env' = M.insert r_v (Just (TRefined r_vt r,
                                                   VPMulti [VPId r_v, r_vp]))
                                            env
                    return $ zip (map fst succs) (repeat env')
                | otherwise -> subtypeError p "CallStmt retval" r_vt r
          Just (typeArgs,_,_,_,_) -> do
            -- This should not happen:
            -- forall a b c. forall x y z . int -> bool
            liftIO $ putStrLn $ "typeargs: " ++ show typeArgs
            catastrophe p("application still has uninstantiated type variables:"
                           ++ show typeArgs)               
         
    IfStmt (_, p) e s1 s2 -> do
      (t, vp) <- expr env ee e -- this permits non-boolean tests
      assertSubtype p "IfStmt" t boolType
      assert (length succs == 2) "IfStmt should have two successors"
      let occurit (node, Nothing) = error "ifstmt's branches should have lits!"
          occurit (node, Just (BoolLit _ True)) = (node, gammaPlus env vp)
          occurit (node, Just (BoolLit _ False)) = (node, gammaMinus env vp)
          occurit _ = error "Ifstmt's branches are wack"
      return $ map occurit succs
    WhileStmt _ e s -> do
      expr env ee e -- this permits non-boolean tests
      noop -- will change for occurrence types
    ForInStmt _ id e s -> fail "ForIn NYI"
    TryStmt _ s id catches finally  -> fail "TryStmt NYI"
    ThrowStmt _ e -> do
      expr env ee e
      noop
    ReturnStmt (_,p) Nothing -> do
      assertSubtype p "ReturnStmt undef" undefType rettype
      noop
    ReturnStmt (_,p) (Just e) -> do
      (te, vp) <- expr env ee e
      assertSubtype p "ReturnStmt" te rettype
      noop

    LabelledStmt _ _ _ -> noop
    BreakStmt _ _ -> noop
    ContinueStmt _ _ -> noop
    SwitchStmt _ e cases default_ -> error "switch stmt NYI"

-- in pJS, string, int, etc. can all be used as objects.
-- but they're not objects; they get converted.
-- this function does this conversion
dotrefContext :: Type SourcePos -> TypeCheck (Type SourcePos)
dotrefContext (TId p "string") = do
  state <- get
  let tenv = typeEnv state
  sobj <- resolveAliases tenv (TId p "String")
  return sobj
dotrefContext t = return t

expr :: Env -- ^the environment in which to type-check this expression
     -> ErasedEnv
     -> Expr (Int,SourcePos)
     -> TypeCheck (Type SourcePos, VP) 
expr env ee e = do 
 state <- get
 let tenv = typeEnv state
 case e of 
  VarRef (_,p) id -> do
    (t, vp) <- forceEnvLookup p env id
    case vp of
      VPNone -> return (t, VPId id)
      _      -> return (t, VPMulti [VPId id, vp])
  DotRef (_, loc) e p -> do
    --I'm uneasy about needing all of the following 3 lines
    (t'', _) <- expr env ee e
    t' <- dotrefContext (unRec (refined t''))
    let t = unRec t'
    case t of
      TObject _ props -> case lookup p props of
        Just t' -> return (t', VPNone)
        Nothing -> case p of
          --TODO: make all objs have these fields: 
          "toString" -> return (TFunc [TId loc "any"] Nothing (TId loc "string") LPNone, 
                                VPNone)
          _ -> typeError loc (printf "expected object with field %s" p)
      otherwise -> typeError loc (printf "expected object, received %s"
                                         (show t))
                                         
  BracketRef (_, loc) e ie -> do
    (t'', _) <- expr env ee e
    t' <- dotrefContext (unRec (refined t''))
    let t = unRec t'
    (it', _) <- expr env ee ie
    let it = unRec (refined it')
    assertSubtype loc "BracketRef" it (TId loc "int")
    case t of
      TApp _ (TId _ "Array") [btype] -> return (btype, VPNone)
      _ -> fail $ printf "at %s: expected array, got %s" (show loc) (show t)
  OpExpr (_,p) f args_e -> do
    args <- mapM (expr env ee) args_e
    operator p f args
  Lit (StringLit (_,a) s) -> 
    return (TId a "string",
            VPLit (StringLit a s) (TId a "string"))
  Lit (RegexpLit _ _ _ _) -> fail "regexp NYI"
  Lit (NumLit (_,a) n) ->
    return (TId a "double", 
            VPLit (NumLit a n) (TId a "double"))
  Lit (IntLit (_,a) n) -> 
    return (TId a "int",
            VPLit (IntLit a n) (TId a "int"))
  Lit (BoolLit (_,a) v) ->
    return (boolType,
            VPLit (BoolLit a v) boolType)
  Lit (NullLit (_,p)) -> fail "NullLit NYI (not even in earlier work)"
  Lit (ArrayLit (_,p) es) -> do
    r <- mapM (expr env ee) es
    let ts = nub (map (refined . fst) r)
    --TODO: does this type make sense?
    let atype = if length ts == 1 
                  then head ts
                  else TUnion ts
    let vp = VPLit (ArrayLit p (error "dont look inside VP arraylit"))
                   (TApp p (TId p "Array") [atype])
    return (TApp p (TId p "Array") [atype], vp)
  Lit (ObjectLit (_, loc) props) -> do
    let prop (Left s, (_, propLoc), e) = do
          -- the VP is simply dropped, but it is always safe to drop a VP
          (t, vp) <- expr env ee e
          case M.lookup propLoc ee of
            Just [t'] -> do
              assertSubtype propLoc "ObjectLit" t t'
              return (s, t')
            Nothing -> return (s, t)
            Just ts ->
              catastrophe propLoc (printf "erased-env for property is %s" 
                                          (show ts))
          return (s, t) 
        prop (Right n, (_, propLoc), e) = do
          catastrophe propLoc "object literals with numeric keys NYI"
    propTypes <- mapM prop props
    let t = TObject loc propTypes
    return (t, VPNone)
  Lit (FuncLit (_, p) args locals body) -> case M.lookup p ee of
    Nothing -> catastrophe p "function lit is not in the erased environment"
    Just [t] -> do
     case deconstrFnType t of
      Just (_, _, argTypes, _, _) 
        | length argTypes == length args - 1 -> 
            return (t, VPLit (FuncLit p (error "dont look in VP Funclit args")
                                        (error "dont look in VP Funclit lcls")
                                        (error "dont look in VP Funclit body"))
                             t)
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
  let numeric requireInts returnDouble = do
        assertSubtype loc "numeric op lhs" lhs
          (if requireInts then intType else doubleType)
        assertSubtype loc "numeric op rhs" rhs
          (if requireInts then intType else doubleType)
        if returnDouble
          then return $ novp doubleType
          else return $ novp (if lhs <: intType then rhs else lhs)

  case op of
    OpLT -> cmp
    OpLEq -> cmp
    OpGT -> cmp
    OpGEq -> cmp 
    OpIn -> fail "OpIn NYI"
    OpInstanceof -> fail "OpInstanceof NYI"

    OpEq        -> return (boolType, equalityvp lvp rvp)
    OpStrictEq  -> return (boolType, equalityvp lvp rvp)
    OpNEq       -> return (boolType, 
                           VPNot (equalityvp lvp rvp))
    OpStrictNEq -> return (boolType, 
                           VPNot (equalityvp lvp rvp))

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
    OpAdd | lhs <: stringType || rhs <: stringType -> return $ novp stringType
          | otherwise -> numeric False False
    PrefixLNot -> do
      --assertSubtype loc "prefixLNot" lhs boolType
      case lvp of
        VPNot v -> return (boolType, v)
        v -> return (boolType, VPNot v)
    PrefixBNot -> do
      assertSubtype loc "PrefixBNot"lhs intType
      return $ novp intType
    PrefixMinus -> do
      assertSubtype loc "PrefixMinus" lhs doubleType 
      return $ novp lhs
    PrefixVoid -> do
      catastrophe loc (printf "void has been removed")
    PrefixTypeof ->
      let tproc (VPId i) = VPTypeof i
          tproc (VPMulti vs) = VPMulti (nub (map tproc vs))
          tproc _ = VPNone
       in return (stringType, tproc lvp)

-- |When a node has multiple parents, this function combines their environments.
unionEnv :: Env -> Env -> Env
unionEnv env1 env2 =
  foldl' (\env (id, maybeType) -> M.insertWith unionTypeVP id maybeType env)
         env1 (M.toList env2)

uneraseEnv :: Env -> Map String (Type SourcePos)
              -> ErasedEnv -> Lit (Int, SourcePos) 
              -> TypeCheck (Env, Type SourcePos)
uneraseEnv env tenv ee (FuncLit (_, pos) args locals _) = do
  let lookupEE p name = case M.lookup p ee of
        Nothing -> return Nothing
        Just t | head name == '@' -> return Nothing
               | otherwise -> do
                   --liftIO $ putStrLn $ "Got: " ++ show t
                   t' <- mapM (resolveAliases tenv) t
                   --liftIO $ putStrLn $ "Yield: " ++ show t'
                   return $ Just t'
      functype' = head $ case M.lookup pos ee of
                          Nothing -> -- fake it. TODO: fix this bug for real.
                            [(TFunc [TId noPos "undefined"] Nothing 
                                (TId noPos "undefined") LPNone)]
                          Just xx -> xx
  functype <- resolveAliases tenv functype'
  let Just (_, cs, types, rettype, lp) = deconstrFnType functype
      -- undefined for arguments
  let (this:types') = types
  argtypes <- return $ zip (map fst args) (map Just (this:undefined:types'))
  localtypes <- mapM (\(name,(_, pos)) -> do
                        t <- lookupEE pos name
                        return (name, liftM head t))
                     locals
      --the only typed things here are args and explicitly typed locals, both
      --of which have VPId name. if it doesn't have a type, it's an ANF var,
      --and it will be given one in due time.
  let novp (a,Just t)  = (a, Just (t, VPId a))
      novp (a,Nothing) = (a, Nothing)
      env' = M.union (M.fromList (map novp $ argtypes++localtypes)) env 
  return (env', rettype)

uneraseEnv env tenv ee _ = error "coding fail - uneraseEnv given a function-not"

typeCheckProgram :: Env
                  -> (Tree ErasedEnv, 
                      Tree (Int, Lit (Int,SourcePos), Graph))
                  -> TypeCheck Env
typeCheckProgram env (Node ee' subEes, Node (_, lit, gr) subGraphs) = do
  state <- get
  put $ state { stateGraph = gr, stateEnvs = M.empty }
  -- When type-checking the body, we assume the declared types for functions.
  ee <- resolveAliasesEE (typeEnv state) ee'
  (env', rettype) <- uneraseEnv env (typeEnv state) ee lit
  topLevelEnv <- body env' ee rettype (enterNodeOf gr) (exitNodeOf gr)
  -- When we descent into nested functions, we ensure that functions satisfy
  -- their declared types.
  -- This handles mutually-recursive functions correctly.  
  unless (length subEes == length subGraphs) $
    fail "erased env and functions have different structures"
  mapM_ (typeCheckProgram env') (zip subEes subGraphs)
  return topLevelEnv

-- |Take a type environment and a type, and return a type with all the
-- |aliases resolved (e.g. TId "DOMString" --> TId "string").
-- |Fail if the TId is not in the environment.
-- TODO: add a "reAlias" func to make error messages nicer =).
-- TODO: this is the func that should handle <- .
resolveAliases :: (MonadIO m) => (Map String (Type SourcePos)) 
                  -> (Type SourcePos) -> m (Type SourcePos)
resolveAliases tenv t@(TId pos i)
 | i == "string"    = return t
 | i == "int"       = return t
 | i == "double"    = return t
 | i == "bool"      = return t
 | i == "Array"     = return t -- TODO: handle 'generics' properly
 | i == "undefined" = return t
 | i == "any"       = return t
 | otherwise        = case M.lookup i tenv of
     Nothing -> return t {-fail $ printf "at %s: type %s is unbound. (env=%s)" 
                         (show pos) (show t) (show tenv)-}
     Just x -> return x
resolveAliases tenv (TRec s t) = do
  --TODO: is this right? I temporarily insert 's' into the tenv so it gets
  -- left alone.
  t' <- resolveAliases (M.insert s (TId noPos s) tenv) t
  return (TRec s t')
resolveAliases tenv (TFunc req var ret lp) = do
  req' <- mapM (resolveAliases tenv) req
  var' <- case var of
    Nothing -> return Nothing
    Just blah -> do
      res <- resolveAliases tenv blah
      return (Just res)
  ret' <- resolveAliases tenv ret
  return (TFunc req' var' ret' lp)
resolveAliases tenv (TObject pos fields) = do
  fields' <- mapM (\(s, t) -> do
                     t' <- resolveAliases tenv t
                     return (s, t')) fields
  return (TObject pos fields')
resolveAliases tenv (TApp pos tapp ts) = do
  tapp' <- resolveAliases tenv tapp
  ts' <- mapM (resolveAliases tenv) ts
  return (TApp pos tapp' ts')
resolveAliases tenv (TUnion ts) = do
  ts' <- mapM (resolveAliases tenv) ts
  return (TUnion ts')
resolveAliases tenv (TForall ss cs t) = do
  --make the function ignore all types the forall defines
  t' <- resolveAliases (M.unions $ (map (\k->M.singleton k (TId noPos k)) ss)++
                                   [tenv]) t
  return (TForall ss cs t')                                   
resolveAliases tenv (TRefined t1 t2) = fail "What is TRefined doing in alias?"
  
resolveAliases tenv t = fail $ "resolveAliases can't handle " ++ show t

resolveAliasesEE :: (MonadIO m) => (Map String (Type SourcePos)) 
                  -> ErasedEnv -> m ErasedEnv
resolveAliasesEE tenv ee = do
  --not sure if there is a more efficient way to do this:
  let procp (k, v) = do
        v' <- mapM (resolveAliases tenv) v
        return (k, v')
  resl <- mapM procp (M.toList ee)
  return $ M.fromList resl

--type ErasedEnv = Map SourcePos [Type SourcePos]

{-
  | TApp a (Type a) [Type a]
  | TUnion [Type a]
  | TForall [String] [TypeConstraint] (Type a)
  -- | TIndex (Type a) (Type a) String --obj[x] --> TIndex <obj> <x> "x"
  --the first type, 'refined' to the 2nd
  | TRefined (Type a) (Type a) 
-}

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

  -- load the global environment from "core.js"
  dir <- getDataDir
  toplevels' <- parseFromFile (parseToplevels) (dir </> "core.tjs")
  toplevels <- case toplevels' of
    Left err -> fail $ "PARSE ERROR ON CORE.TJS: " ++ show err
    Right tls -> return tls

  let procTLs :: (MonadIO m) => [TJS.ToplevelStatement SourcePos]
                 -> (Env, Map String (Type SourcePos))
                 -> m (Env, Map String (Type SourcePos))
      procTLs [] results = return results
      procTLs ((TJS.ExternalStmt _ (TJS.Id _ s) t):rest) (venv, tenv) = do
        t' <- resolveAliases tenv t
        procTLs rest (M.insertWithKey 
                        (\k n o -> error $ "already in venv: " ++ show k)
                        s (Just (t', VPId s)) venv, tenv)
      procTLs ((TJS.TypeStmt _ (TJS.Id _ s) t):rest) (venv, tenv) = do
        t' <- resolveAliases tenv t
        procTLs rest (venv, M.insertWithKey
                              (\k n o -> error $ "already in tenv: " ++ show k)
                              s t' tenv)
        
  --TODO: pass typeenv in the state monad
  (globalVarEnv', globalTypeEnv) <- procTLs toplevels (M.empty, M.empty)
  let globalVarEnv = M.unions $ [globalVarEnv'] ++ 
        [M.fromList [("this", Just (TObject noPos [], VPId "this"))]]
  
  (env, state) <- runStateT (typeCheckProgram globalVarEnv (envs, intraprocs)) 
                            (TypeCheckState G.empty M.empty globalTypeEnv)
  return env

