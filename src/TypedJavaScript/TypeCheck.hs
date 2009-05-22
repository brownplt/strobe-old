module TypedJavaScript.TypeCheck where

import TypedJavaScript.PrettyPrint
import TypedJavaScript.Prelude
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Graph.Inductive as G
import Control.Monad.State.Strict
import qualified TypedJavaScript.Syntax as TJS
import TypedJavaScript.Syntax (Type (..), TypeConstraint (..), VP (..), 
  LatentPred (..))
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
import BrownPLT.TypedJS.InitialEnvironment
import BrownPLT.TypedJS.TypeFunctions
import BrownPLT.JavaScript.Analysis.DefineBeforeUse
import BrownPLT.TypedJS.ReachableStatements

import Paths_TypedJavaScript
import Text.ParserCombinators.Parsec (parseFromFile)
import TypedJavaScript.Parser (parseToplevels)


import System.Directory
import System.FilePath

data TypeCheckState = TypeCheckState {
  stateGraph :: Graph,
  stateEnvs :: Map Int Env,
  stateTypeEnv :: Map String Type
}


basicKinds :: KindEnv
basicKinds = M.fromList
  [ ("int", KindStar)
  , ("bool", KindStar)
  , ("string", KindStar)
  , ("double", KindStar)
  , ("undefined", KindStar)
  , ("Array", KindConstr [KindStar] KindStar)
  ]


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

subtypeError loc msg  s t = 
  fail $ printf "at %s: %s, expected subtype of %s, got %s" (show loc) msg
                (renderType s) (renderType t)


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
     -> [TypeConstraint]
     -> Type
     -> G.Node
     -> G.Node
     -> TypeCheck Env
body env ee constraints rettype enterNode exitNode = do
  state <- get
  let t1 <: t2 = isSubType (stateTypeEnv state) constraints t1 t2
  -- TODO: ensure that the subgraph is connected, probably in 
  -- javascript-analysis
  let gr = stateGraph state
  -- Enter has no predecessors
  unless (null $ G.pre gr enterNode) $
    fail $ "Unexpected edges into  " ++ show (G.lab gr enterNode)

  let (nodes,removedEdges) = topologicalOrder gr enterNode

  mapM_ (stmtForBody env ee constraints rettype) nodes

  finalLocalEnv <- lookupLocalEnv (exitNodeOf gr)
  return finalLocalEnv


stmtForBody :: Env -- ^environment of the enclosing function for a nested
                   -- function, or the globals for a top-level statement or
                   -- function
            -> ErasedEnv
            -> [TypeConstraint]
            -> Type
            -> G.Node
            -> TypeCheck ()
stmtForBody enclosingEnv erasedEnv constraints rettype node = do
  localEnv <- lookupLocalEnv node
  s <- nodeToStmt node
  succs <- stmt (M.union localEnv enclosingEnv) erasedEnv constraints rettype 
                node s
  mapM_ updateLocalEnv succs
    


-- |Lookup a list of types in an erased-environment.  Signals a catastrophe if
-- no such list exists.
--
-- This is to typecheck 'CallStmt'.
forceLookupMultiErasedEnv :: Monad m 
                          => ErasedEnv -> SourcePos 
                          -> m [Type]
forceLookupMultiErasedEnv ee p = case M.lookup p ee of
  Nothing -> catastrophe p "expected a list of types in the erased environment"
  Just ts -> return ts


forceEnvLookup :: Monad m
               => SourcePos -> Env -> Id -> m (Type, Type, Bool, VP)
forceEnvLookup loc env name = case M.lookup name env of
  Nothing -> 
    fail $ printf "at %s: identifier %s is unbound" (show loc) name
  Just Nothing -> 
    fail $ printf "at %s: identifier %s is uninitialized" (show loc) name
  Just (Just t) -> return t

assert :: Monad m => Bool -> String -> m ()
assert True _ = return ()
assert False msg = fail ("CATASPROPHIC FAILURE: " ++  msg)

doAssignment :: (Monad m) 
             => (Type -> Type -> Bool) -- ^local subtype relation
             -> SourcePos -- ^for type errors
             -> Env -- ^current environment
             -> Id -- ^LHS of assignment
             -> Type -- ^type of the RHS of assignment
             -> VP  -- ^visible predicate on the RHS
             -> m Env -- ^resulting environment
doAssignment (<:) p env v te e_vp = case M.lookup v env of        
  Nothing -> typeError p (v ++ " is unbound")
  -- ANF variable, or locally inferred variable.  ANF variables may be
  -- assigned to multiple times in parallel branches, 
  -- possibly creating a union in unionEnv.
  -- Locally inferred variables may also be assigned to multiple times.
  -- However, since their initialization dominates subsequent assignments,
  -- they will subsequently act as declared variables and won't be permitted
  -- to "change types."
  Just Nothing -> do 
    return $ M.insert v (Just (te, te, True,
                               VPMulti [VPId v, e_vp])) env
  -- Local variable (3rd element of the tuple is True).  Local variables
  -- may be assigned to so long as the subtype relation is preserved.  The
  -- assignment locally refines tDec to te.
  Just (Just (tDec, tAct, True, v_vp)) --local variable
    | te <: tDec ->  do
        -- TODO: remove, from environment, any VP referring to this var!
        let env' = M.insert v (Just (tDec, te, True, VPMulti [VPId v, v_vp])) 
                            env
        return env'
   | otherwise -> typeError p $
       printf "assigning to %s :: %s; given an expression of type %s"
              v (renderType tDec) (renderType te)
  -- Variable in an enclosing scope.  If its type is a union, it is possible
  -- that a function in the dynamic calling context has locally refined tDec to
  -- a more precise type.  Due to such cases, we cannot permit any assignment
  -- to unions in enclosing scopes.
  -- If the variable is not a union, we may assign a new value.  However, this
  -- precludes visible-predicates from refining types to specific /values/.
  -- For example, we cannot refine to false.
  Just (Just (tDec, tAct, False, v_vp))
    | isUnion tDec -> typeError p $ 
        printf "cannot assign to global union %s :: %s"
               v (renderType tDec)
    | isAny tDec -> typeError p "cannot assign to global anys"
    | te <: tDec ->  do
        -- TODO: remove, from environment, any VP referring to this var!
        let env' = M.insert v (Just (tDec, te, False,
                                     VPMulti [VPId v, v_vp])) 
                            env
        return env'
   | otherwise -> typeError p $
       printf "assigning to %s :: %s; given an expression of type %s"
              v (renderType tDec) (renderType te)

stmt :: Env -- ^the environment in which to type-check this statement
     -> ErasedEnv
     -> [TypeConstraint]
     -> Type
     -> G.Node -- ^the node representing this statement in the graph
     -> Stmt (Int, SourcePos)
     -> TypeCheck [(G.Node, Env)]
stmt env ee cs rettype node s = do
  state <- get
  let t1 <: t2 = isSubType (stateTypeEnv state) cs t1 t2
  let tenv = stateTypeEnv state
  succs <- stmtSuccs s
  -- statements that do not affect the incoming environment are "no-ops"
  let noop = return (zip (map fst succs) (repeat env))
  case s of
    EnterStmt _ -> noop
    ExitStmt (exitNode, p) -> do
      -- All predecessors of Exit must be ReturnStmt
      let gr = stateGraph state
      let returns = map (G.lab gr) (G.pre gr exitNode)
      let assertReturn maybeStmt = case maybeStmt of
            Nothing -> catastrophe p "predecessor of an Exit node is \
                                       \unlabelled in the CFG"
            Just (ReturnStmt _ _) -> return ()
            Just s | undefType <: rettype -> return ()
                   | otherwise -> typeError (snd $ stmtLabel s) 
                                    "expected return after this statement"
      mapM_ assertReturn returns
      when (null returns && not (undefType <: rettype)) $ do
        liftIO $ putStrLn (show returns)
        typeError p $ printf "no return value, return type is %s" 
                             (renderType rettype)
      noop
    SeqStmt{} -> noop
    EmptyStmt _ -> noop

    -- x :: Array<t> = [ ]
    AssignStmt (_,p) v (Lit (ArrayLit _ [])) -> case M.lookup v env of
      Just (Just (_, TApp "Array" [t], _, _)) ->
        noop
      -- Usually caused by the arguments array of zero-arity functions.
      Just Nothing -> do
        let env' = M.insert v 
                     (Just (TSequence [] Nothing, TSequence [] Nothing, 
                            True, VPNone)) env
        return (zip (map fst succs) (repeat env'))
      Nothing ->
        fail $ printf "%s is unbound at %s" v (show p)
      Just (Just (_, t, _, _)) -> 
        typeError p (printf "[] is an array; given type: %s" (renderType t))
    
    AssignStmt (_,p) v e -> do
      (te,e_vp) <- expr env ee cs e
      env' <- doAssignment (<:) p env v te e_vp
      return $ zip (map fst succs) (repeat env')

    -- THE FOLLOWING IS MUTATION!!! WARNING!!! CHIDLREN WILL GET HRUT
    -- TODO: make a doMutation function, use it for the following 2 cases
    DirectPropAssignStmt (_,p) obj prop e -> do
      (t_rhs, e_vp) <- expr env ee cs e
      case M.lookup obj env of
        Nothing -> 
          catastrophe p (printf "id %s for an object is unbound" obj)
        Just Nothing -> do
          -- Variable is in scope but is yet to be defined.
          fail $ printf "at %s: can't assign to obj %s; has no type yet"
                   (show p) obj
        Just (Just (tDec, tAct', isLocal, vp)) -> do
         tAct <- dotrefContext tAct'
         case unRec tAct of
          TObject _ props -> case lookup prop props of
            Nothing -> 
              typeError p (printf "object does not have the property %s" prop)
            -- TODO: detect if a field was discovered and, if so,
            -- disallow mutation to it.
            Just t' | isUnion t' -> typeError p $ 
                        printf "cannot mutate to a union field"
                    | isSlackObject t' -> typeError p $
                        printf "cannot mutate the field %s :: %s"
                               prop (renderType t')
                    | t_rhs <: t' -> noop -- TODO: affect VP?
                    | otherwise -> 
                        subtypeError p "assignment to property" t_rhs t'
          t' -> typeError p $ printf "expected object, received %s" 
                  (renderType t')
          
    IndirectPropAssignStmt (_,p) obj method e -> do 
      (t_rhs, _) <- expr env ee cs e
      case (M.lookup obj env, M.lookup method env) of
        (Just (Just (_, TApp "Array" [t_elem], isLocal, _)), 
         Just (Just (_, t_prop, _, _)))
          | isUnion t_elem -> typeError p $
              printf "cannot mutate to a union element of an array"
          | isObject t_elem -> typeError p $
              printf "cannot mutate to an object element of an array"
          | t_prop <: intType && t_rhs <: t_elem -> 
              noop
          | t_prop <: stringType ->
              subtypeError p "array insertion" t_rhs t_elem
          | otherwise -> do
              if (not $ t_prop <: intType)
                then subtypeError p "array index not an integer" intType t_prop
                else subtypeError p "array rhs wrong" t_elem t_rhs
        (Just (Just (_, TApp "Array" [t_elem], _, _)), Just Nothing) ->
          typeError p (printf "index variable %s is undefined" method)
        z -> do
          liftIO $ putStrLn (show z)
          typeError p "error assigning to an array element"
    DeleteStmt _ r del -> fail "delete NYI"
    NewStmt{} -> fail "NewStmt will be removed from ANF"
    CallStmt (_,p) r_v f_v args_v -> do
        (_, f, f_isLocal, f_vp) <- forceEnvLookup p env f_v
        -- explicitly instantiated type-variables when calling polymorphic
        -- functions
        insts <- forceLookupMultiErasedEnv ee p
        actualsWithVP' <- liftM (map (\(_, t, _, vp) -> (t, vp)))
                                (mapM (forceEnvLookup p env) args_v)
        let (this':arguments:actuals', actuals_vps) = unzip actualsWithVP'
        this <- dotrefContext this' --motivation: if 'this' is a
                                    --string, int, etc, it is automatically
                                    --converted to an object.
         
        --actuals_vps contains VP, including VPId for the var name itself.
        let actuals = this:arguments:actuals'
        case deconstrFnType f of
          Nothing -> typeError p ("expected function; received " ++ show f)
          Just (vs, cs', formals', vararg, r, latentPred) -> do
            unless (length vs == length insts) $ do
              typeError p (printf "expected %d type argument(s), received %d"
                                  (length vs) (length insts))

            let checkInst (t, v, TCSubtype _ t')
                  | t <: t' = return (TCSubtype v t)
                  | otherwise = typeError p $ printf
                      "supplied type %s for %s does not satisfy the %s <: %s"
                        (renderType t) v v (renderType t')

            instConstraints <- mapM checkInst (zip3 insts vs cs')

            let t1 <: t2 = isSubType (stateTypeEnv state) 
                                     (instConstraints ++ cs' ++ cs) 
                                      t1 t2
            
            let substVar (v, t) t' = substType v t t'
            let apply t = foldr substVar t (zip vs insts)
            r <- return (apply r)
            formals' <- return (map apply formals')

            --if we have a vararg, repeat the vararg until we have as
            --many formals as actuals:
            let formals = case vararg of
                            Nothing -> formals'
                            Just vt -> formals' ++ 
                              (take (length actuals - length formals') 
                                    (repeat (apply vt)))
            let (supplied, missing) = splitAt (length actuals) formals
            when (length actuals > length formals) $ do
              typeError p (printf "function expects %d arguments, but %d \
                                  \were supplied" (length formals)
                                  (length actuals))
            let checkArg (actual,formal) = do
                  unless (actual <: formal) $ do
                    subtypeError p "function call arguments" formal actual
            let (athis:aargs:areals) = actuals
            let (sthis:sargs:sreals) = supplied
            mapM_ checkArg (zip (athis:areals) (sthis:sreals))
            let checkMissingArg actual = do
                  unless (undefType <: actual) $
                    typeError p (printf "non-null argument %s not supplied"
                                        (show actual))
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
            env' <- doAssignment (<:) p env r_v r r_vp
            return $ zip (map fst succs) (repeat env')

    IfStmt (_, p) e s1 s2 -> do
      (t, vp) <- expr env ee cs e -- this permits non-boolean tests
      assert (length succs == 2) "IfStmt should have two successors"
      let occurit (node, Nothing) = error "ifstmt's branches should have lits!"
          occurit (node, Just (BoolLit _ True)) = (node, gammaPlus env vp)
          occurit (node, Just (BoolLit _ False)) = (node, gammaMinus env vp)
          occurit _ = error "Ifstmt's branches are wack"
      return $ map occurit succs
    WhileStmt _ e s -> do
      expr env ee cs e -- this permits non-boolean tests
      noop -- will change for occurrence types
    ForInStmt (_,p) id e s -> do
      unless (isVarRef e) $
        typeError p (printf "can only forin through a named object, given %s"
                       (show e))
      let VarRef _ oid = e
      (t, vp) <- expr env ee cs e
      case t of
        TObject _ fields ->        
          case M.lookup id env of 
            Nothing -> typeError p
              (printf "id %s for forin loop is unbound" id)
            Just (Just (tDec, tAct', isLocal, vp)) -> typeError p 
              (printf "id %s already has a type in a forin, but it shouldnt")
            Just Nothing -> do
              let env' = M.insert id
                           (Just (TIterator oid, TIterator oid, 
                                  True, VPNone)) env
              return (zip (map fst succs) (repeat env'))
        _ -> typeError p (printf "trying to forin through %s, not obj" 
                            (renderType t))

-- Lit (StringLit (_,a) s) -> 

{-      Just Nothing -> do
        let env' = M.insert v 
                     (Just (TSequence [] Nothing, TSequence [] Nothing, 
                            True, VPNone)) env
        return (zip (map fst succs) (repeat env'))

          M.insert 
          fail $ printf "at %s: can't assign to obj %s; has no type yet"
                   (show p) obj


      let itype = TIterator 
      fail "ForIn NYI" -}
    TryStmt _ s id catches finally  -> fail "TryStmt NYI"
    ThrowStmt _ e -> do
      expr env ee cs e
      noop
    ReturnStmt (_,p) Nothing 
      | undefType <: rettype -> noop
      | otherwise -> subtypeError p "return;" undefType rettype
    ReturnStmt (_,p) (Just e) -> do
      (te, vp) <- expr env ee cs e
      if (te <: rettype)
        then noop
        else typeError p (printf "function is declared to return %s, but this \
                                 \statement returns %s" (show rettype) 
                                 (show te))
    LabelledStmt _ _ _ -> noop
    BreakStmt _ _ -> noop
    ContinueStmt _ _ -> noop
    SwitchStmt (i,p) id cases default_ -> do
      --assumption: succs contains the same lits that cases does
      (t, vp) <- expr env ee cs (VarRef (i,p) id)
      let occurit (node, Just lit) = do
            (tlit, vplit) <- expr env ee cs (Lit lit)
            return (node, gammaPlus env (equalityvp vp vplit))
          occurit (node, Nothing) = do --default branch
            tsvps <- mapM (expr env ee cs . Lit) (map fst cases)
            return (node,foldl gammaMinus env (map (equalityvp vp . snd) tsvps))
      mapM occurit succs

-- in pJS, string, int, etc. can all be used as objects.
-- but they're not objects; they get converted.
-- this function does this conversion
dotrefContext :: Type -> TypeCheck (Type)
dotrefContext t = do
  state <- get
  let tenv = stateTypeEnv state
      mobj = case t of
               TId "string" -> M.lookup "String" tenv
               TId "int"    -> M.lookup "Number" tenv
               TId "double" -> M.lookup "Number" tenv
               TId "bool"   -> M.lookup "Boolean" tenv
               _            -> Just t
  case mobj of
    Nothing -> fail $ "core.js is broken: String/Number/Boolean is missing"
    (Just obj) -> return obj

lookupConstraint :: Type -> [TypeConstraint] -> Type
lookupConstraint t [] = t
lookupConstraint t@(TId x) (tc:tcs) = case tc of
  TCSubtype y t | x == y -> t
  otherwise -> lookupConstraint t tcs

lookupConstraint t (tc:tcs) = case tc of
  TCSubtype t1 t2 | isSubType M.empty [] t (TId t1) -> t2
                  | otherwise -> lookupConstraint t tcs
  

expr :: Env -- ^the environment in which to type-check this expression
     -> ErasedEnv
     -> [TypeConstraint]
     -> Expr (Int,SourcePos)
     -> TypeCheck (Type, VP) 
expr env ee cs e = do 
  state <- get
  let t1 <: t2 = isSubType (stateTypeEnv state) cs t1 t2
  let unConstraint t = lookupConstraint t cs
  let tenv = stateTypeEnv state
  case e of 
   VarRef (_,p) id -> do
     (tDec, tAct, b, vp) <- forceEnvLookup p env id
     case vp of
       VPNone -> return (tAct, VPId id)
       _      -> return (tAct, VPMulti [VPId id, vp])
   DotRef (_, loc) e p -> do
     --I'm uneasy about needing all of the following 3 lines.
     -- but why? - arjun
     (t'', _) <- expr env ee cs e
     t' <- dotrefContext (unRec t'')
     let t = unConstraint (unRec t')
     case fieldType p t of
       Just t' -> return (t', VPNone)
       Nothing -> typeError loc $ printf
         "expected object with field %s, received %s" p (renderType t)
   BracketRef (_, loc) e ie -> do
     (t'', _) <- expr env ee cs e
     t' <- dotrefContext (unRec t'')
     let t = unRec t'
     (it', _) <- expr env ee cs ie
     let it = unRec it'
     case t of
       TApp "Array" [btype]
         | not (it <: intType) -> subtypeError loc "obj[prop]" intType it
         | otherwise -> return (btype, VPNone)
       TObject _ props
         | isVarRef e -> case it of
             TIterator z -> do
               let (VarRef _ ename) = e
               if ename == z
                 then return (TProperty ename, VPNone)
                 else typeError loc $ printf "fail to obj[prop]: obj's name \
                                           \doesn't match name iterator is for"
             _ -> typeError loc (printf "can only bracketref obj with iterator")
       _ -> fail $ printf "at %s: expected array, got %s" (show loc) (show t)
   OpExpr (_,p) f args_e -> do
     args <- mapM (expr env ee cs) args_e
     operator cs p f args
   Lit (StringLit (_,a) s) -> 
     return (TId "string",
             VPLit (StringLit a s) (TId "string"))
   Lit (RegexpLit _ _ _ _) -> fail "regexp NYI"
   Lit (NumLit (_,a) n) ->
     return (TId "double", 
             VPLit (NumLit a n) (TId "double"))
   Lit (IntLit (_,a) n) -> 
     return (TId "int",
             VPLit (IntLit a n) (TId "int"))
   Lit (BoolLit (_,a) v) ->
     return (boolType,
             VPLit (BoolLit a v) boolType)
   Lit (NullLit (_,p)) -> fail "NullLit NYI (not even in earlier work)"
   Lit (ArrayLit (_,p) es) -> do
     r <- mapM (expr env ee cs) es
     let ts = map fst r
     
     case ts of
       [] -> typeError p "empty array needs a type"
       (t:ts) -> do 
         let tRes = TApp "Array" [foldr unionType t ts]
         return $ (tRes, VPLit (ArrayLit p (error "VP of ArrayLit NYI"))
                               tRes)
     
   Lit (ArgsLit (_,p) es) -> do
     r <- mapM (expr env ee cs) es
     let ts = map fst r
     let resT = (TSequence ts Nothing)
     let vp = VPLit (ArgsLit p (error "dont look inside VP argslit"))
                    resT
     return (resT, vp)

   Lit (ObjectLit (_, loc) props) -> do
     let prop (Left s, (_, propLoc), e) = do
           -- the VP is simply dropped, but it is always safe to drop a VP
           (t, vp) <- expr env ee cs e
           case M.lookup propLoc ee of
             Just [t'] | t <: t' -> return (s, t')
                       | otherwise -> subtypeError propLoc "{ ... }" t t'
             Nothing -> return (s, t)
             Just ts ->
               catastrophe propLoc (printf "erased-env for property is %s" 
                                           (show ts))
           return (s, t) 
         prop (Right n, (_, propLoc), e) = do
           catastrophe propLoc "object literals with numeric keys NYI"
     propTypes <- mapM prop props
     return (TObject False propTypes, VPNone)
   Lit (FuncLit (_, p) args locals body) -> case M.lookup p ee of
     Nothing -> catastrophe p "function lit is not in the erased environment"
     Just [t] -> do
      case deconstrFnType t of
       Just (_, _, argTypes, _, _, _) 
         --argtypes is ("thistype", argarraytype, real args)
         --args should be is ("this", "arguments", real args)
         | length argTypes == length args -> 
             return (t, VPLit (FuncLit p (error "dont look in VP Funclit args")
                                         (error "dont look in VP Funclit lcls")
                                         (error "dont look in VP Funclit body"))
                              t)
         | otherwise -> typeError p $ 
             printf "argument number mismatch in funclit: %s args named, but \
                    \%s in the type:%s\n%s\n"
               (show (length args - 2)) (show (length argTypes - 2))
               (renderType t) (show $ map renderType argTypes)
       Nothing -> typeError p $ printf "not a function type: %s" (renderType t)
     Just _ -> catastrophe p "many types for function in the erased environment"
  
operator :: [TypeConstraint]
         -> SourcePos 
         -> FOp 
         -> [(Type, VP)] 
         -> TypeCheck (Type, VP)
operator cs loc op argsvp = do
  state <- get
  let t1 <: t2 = isSubType (stateTypeEnv state) cs t1 t2
  let (args, vps) = unzip argsvp
  -- The ANF transform gaurantees that the number of arguments is correct for
  -- the specified operator.
  let novp t = (t, VPNone)
  
  let lhs = args !! 0
  let rhs = args !! 1 -- Do not use rhs if op takes just one argument!
  let lvp = vps !! 0
      rvp = vps !! 1                      
  let cmp = do
        unless ((lhs <: stringType && rhs <: stringType) ||
                ((lhs <: doubleType || lhs <: intType) && 
                 (rhs <: doubleType || rhs <: intType))) $ do
          typeError loc (printf "can only compare numbers and strings")
        return $ novp boolType
  let numeric requireInts returnDouble = do
        let result = if returnDouble 
                       then return (novp doubleType)
                       else return $ novp (if lhs <: intType then rhs else lhs)
        case requireInts of
          True -> do
            unless (lhs <: intType && rhs <: intType) $
              typeError loc $ printf "operator expects int arguments, given %s \
                                     \and %s" (renderType lhs) (renderType rhs)
            result
          False -> do
            unless  ((lhs <: intType || lhs <: doubleType) &&
                     (rhs <: intType || rhs <: doubleType)) $
              typeError loc $ printf "operator expects double/int arguments, \
                                     \given %s and %s" (renderType lhs)
                                     (renderType rhs)
            result
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
      case lvp of
        VPNot v -> return (boolType, v)
        v -> return (boolType, VPNot v)
    PrefixBNot | lhs <: intType -> return (novp intType)
               | otherwise -> subtypeError loc "!expr" lhs intType
    PrefixMinus | lhs <: doubleType -> return (novp lhs)
	              | lhs <: intType -> return (novp lhs)
                | otherwise -> typeError loc "prefix - expects int/double"
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

-- |Returns the local environment for a function, type constraints in its
-- signature, its return type and its full type.
uneraseEnv :: Env -> Map String Type
           -> Map String Kind
           -> ErasedEnv -> Lit (Int, SourcePos) 
           -> TypeCheck (Env, [TypeConstraint], Type, Type)
uneraseEnv env tenv kindEnv ee (FuncLit (_, pos) args locals _) = do          
  let newNames = map fst (args ++ locals)
  unless (newNames == nub newNames) $ do
    typeError pos "duplicate argument/local names"
  functype <- case M.lookup pos ee of
        Just [t] -> return t
        Nothing -> fail $ "uneraseEnv: no type for function at " ++ show pos
        Just ts -> 
          fail $ printf "uneraseEnv: multiple types for the function at %s, \
                         \types were %s" (show pos) (show ts)

  let Just (tVars, cs, types, vararg, rettype, lp) = deconstrFnType functype
  
  let localKindEnv = M.union (freeTypeVariables functype) kindEnv  

  let lookupEE p name = case M.lookup p ee of
        Nothing -> return Nothing
        Just t | head name == '@' -> return Nothing
               | otherwise -> return (Just t)
               
  let (this:argsarray:types') = types ++ (case vararg of
        Nothing -> []
        Just vt -> [TApp "Array" [vt]])
  argtypes <- return $ zip (map fst args) (map Just (this:argsarray:types'))
  localtypes <- mapM (\(name,(_, pos)) -> do
                        t' <- lookupEE pos name
                        case t' of
                          Nothing -> return (name, Nothing)
                          Just [] -> fail "Uhm... "
                          Just (t:rest) -> do
                            return (name, Just t))
                     locals
      --the only typed things here are args and explicitly typed locals, both
      --of which have VPId name. if it doesn't have a type, it's an ANF var,
      --and it will be given one in due time.
  let novp (a,Just t)  = (a, Just (t, t, True, VPId a))
      novp (a,Nothing) = (a, Nothing)
      env' = M.union (M.fromList (map novp $ argtypes++localtypes)) env 
  return (env', cs, rettype, functype)

uneraseEnv env tenv ee _ _ = 
  error "coding fail - uneraseEnv given a function-not"

typeCheckProgram :: Env
                 -> KindEnv
                 -> [TypeConstraint]
                 -> (Tree ErasedEnv, 
                     Tree (Int, Lit (Int, SourcePos), Graph))
                 -> TypeCheck Env
typeCheckProgram env enclosingKindEnv constraints
                 (Node ee' subEes, Node (_, lit, gr') subGraphs) = do
  let gr = G.mkGraph (G.labNodes gr') (G.labEdges gr')
  state <- get
  put $ state { stateGraph = gr, stateEnvs = M.empty }
  
  let tenv = stateTypeEnv state
  let ee = M.mapWithKey (replaceAliases enclosingKindEnv tenv) ee'  

  (env', cs, rettype, fnType) <- uneraseEnv env (stateTypeEnv state)
                                            enclosingKindEnv ee lit

  let kindEnv = M.union (freeTypeVariables fnType) enclosingKindEnv
      
  checkDeclaredKinds kindEnv ee
  let cs' = cs ++ constraints
  finalEnv <- body env' ee cs' rettype (enterNodeOf gr) (exitNodeOf gr)
  -- When we descend into nested functions, we ensure that functions satisfy
  -- their declared types.
  -- This handles mutually-recursive functions correctly.  
  unless (length subEes == length subGraphs) $
    fail "CATASTROPHIC FAILURE: erased env and functions have different \
         \structures"
  let localEnv = globalizeEnv finalEnv
  mapM_ (typeCheckProgram localEnv kindEnv cs') (zip subEes subGraphs)
  return localEnv

-- |Checks user-specified type annotations for kind-errors.  We assume that
-- types derived by our type-checker are well-kinded.  Therefore, this is
-- the only kind-check necessary.
checkDeclaredKinds :: Monad m => KindEnv -> ErasedEnv -> m ()
checkDeclaredKinds kinds ee = do
  let check loc type_ = case checkKinds kinds type_ of
        Right KindStar -> return ()
        Right _ -> typeError loc "kind error"
        Left s -> typeError loc ("kind error: " ++ show s)
  let checkAt (loc, types) = mapM_ (check loc) types
  mapM_ checkAt (M.toList ee)
  


loadCoreEnv :: Map String Type
            -> IO (Env, Map String Type)
loadCoreEnv env = do
  let kinds = basicKinds
  -- load the global environment from "core.js"
  dir <- getDataDir
  toplevels' <- parseFromFile (parseToplevels) (dir </> "core.tjs")
  toplevels <- case toplevels' of
    Left err -> fail $ "PARSE ERROR ON CORE.TJS: " ++ show err
    Right tls -> return tls

  let procTLs [] results = return results
      procTLs ((TJS.ExternalStmt _ (TJS.Id _ s) t):rest) (venv, tenv) = do
        procTLs rest (M.insertWithKey 
                        (\k n o -> error $ "already in venv: " ++ show k)
                        s (Just (t, VPId s)) venv, tenv)
      procTLs ((TJS.TypeStmt _ (TJS.Id _ s) t):rest) (venv, tenv) = do
        procTLs rest (venv, M.insertWithKey
                              (\k n o -> error $ "already in tenv: " ++ show k)
                              s t tenv)
  (env, types) <- procTLs toplevels (M.empty, env)

  case checkTypeEnv kinds types of
    Left s -> fail s
    Right () -> do
      let unaliasedTypes = unaliasTypeEnv kinds types
      let unalias Nothing = Nothing -- strange
          unalias (Just (t, vp)) = Just (res, res, False, vp)
            where res = unaliasType kinds unaliasedTypes t                

      return (M.map unalias env, unaliasedTypes)

-- |Type-check a Typed JavaScript program.  
typeCheck :: [TJS.Statement SourcePos] -> IO Env
typeCheck prog = do
  domTypeEnv <- makeInitialEnv
  (venv, tenv) <- loadCoreEnv domTypeEnv 
  typeCheckWithGlobals venv (M.union domTypeEnv tenv) prog


-- convenience function to make testing faster
typeCheckWithGlobals :: Env -> Map String Type -> 
                        [TJS.Statement SourcePos] -> IO Env
typeCheckWithGlobals venv tenv prog = do
  let assertDefUse env anf = 
        case defineBeforeUse (S.fromList (M.keys env)) anf of
          Right () -> return ()
          Left errs ->
            fail $ concat (intersperse "\n" (map f errs))
              where f (v, p) = printf "%s: %s may be used before it is defined"
                                      (show p) v
  let assertReachable procTree = case allReachable procTree of
        Right () -> return ()
        Left p -> fail $ printf "%s: unreachable statements" (show p)

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

  -- add this:
  let venv' = 
        M.insert "this" 
                 (Just (TEnvId "Window", TEnvId "Window", False, VPNone)) venv
  
  assertReachable intraprocs
  assertDefUse venv' (topDecls, anfProg)

  (env, state) <- runStateT (typeCheckProgram venv' basicKinds [] 
                                              (envs, intraprocs)) 
                            (TypeCheckState G.empty M.empty tenv)
  return env
