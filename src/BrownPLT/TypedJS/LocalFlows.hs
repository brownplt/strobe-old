{-# OPTIONS_HADDOCK ignore-exports #-}
module BrownPLT.TypedJS.LocalFlows
  ( BaseType (..)
  , Type (..)
  , localTypes
  , localRefs
  , prettyRefEnv
  , prettyEnv
  , unionType
  ) where

import BrownPLT.TypedJS.Prelude
import BrownPLT.JavaScript.Analysis.ANF
import BrownPLT.JavaScript.Analysis.ANFPrettyPrint
import BrownPLT.JavaScript.Analysis.Intraprocedural
import BrownPLT.JavaScript.Analysis.Graph
import Control.Monad.State
import qualified Data.Graph.Inductive as G
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Text.PrettyPrint.HughesPJ as PP

-- |The types discernable by runtime reflection.  These largely correspond
-- to the possible results of JavaScript's @typeof@ operator.  In addition,
-- we track the values of string literals with @TFixedString@.
data BaseType
  = TNumber
  | TString
  | TBoolean
  | TFunction
  | TObject 
  | TUndefined
  | TFixedString String
  deriving (Show, Eq, Ord)


-- |JavaScript's types are statically indeterminate.  The best we can do is
-- determine that an identifier or an expression has one of a set of types
-- (@TKnown@).  In other cases, a type may be statically unknown (@TUnk@).
-- We distinguish variables whose types are unknown from uninitialized
-- variables (@TUnreachable@).
data Type 
  = TKnown (Set BaseType)
  | TUnk
  | TUnreachable
  deriving (Show, Eq, Ord)


-- |We build an intraprocedural dataflow analysis that determines the type
-- of each variable (i.e. the environment) at each statement.  This is easily
-- done when variables are assigned to literals and simple expressions over
-- literals and variables.
--
-- In addition, the analysis is sensitive to conditionals that are runtime
-- type tests:
--
-- @
--   if (typeof x == \"number\") { ... \/* /x is a number/ *\/ } 
--   else { \/* /x is not a number/ *\/ }
-- @
--
-- The analysis is sound in the presence of assignment, which can change
-- the runtime type of a variable:
--
-- @
--   x = 3;
--   x = \"hello\";
-- @
---
-- Since this is an intraprocedural analysis, it ignores function calls 
-- entirely:
--
-- x = (function() { return 5; })(); \/* x is unknown \*/
--
-- Moreover, the analysis is /unsound/ in the presence of function calls:
--
-- @
--   x = 3; \/* x is a number *\/
--   (function() { x = \"hello\"; })();
--   y = x; \/* analysis reports that x and y are both just numbers *\/
-- @
--
-- However, the analysis is sound if it can assume that function calls do
-- not change the runtime types of variables.  
--
-- When a variable, @x@ is assigned a literal, we know its type.
-- On @x = y@, the type of @typeof x == typeof y@.
--
-- On @x = typeof y@, if we know that @typeof y == t@, we could set @x = t@.
-- However, if @y@ is subsequently reassigned, @y == t@ may no longer hold
-- and we would have to undo the assignment @x = t@.  Therefore, we simply
-- store the reference @x = Typeof y@.  Note that @Typeof y@ is one of
-- a fixed number of strings (@\"number\"@, @\"boolean\"@, etc.)
--
-- @TypeIs@ and @TypeIsNot@ are booleans, dependent on the type of the
-- the referenced variable.  For example:
--
-- @y = typeof x == \"number\"@ is a boolean, dependent on @typeof x@.  When
-- an expression of type @TypeIs@ or @TypeIsNot@ is used as a conditional, we
-- may assume that the expression is either @true@/@false@ either branch.
-- Assuming the value refines the type of @x@ in the environment.
data Ref
  = Type Type
  | Ref Id
  | Typeof Id
  | TypeIs Id Type
  | TypeIsNot Id Type
  deriving (Show, Eq, Ord)


type Env = Map Id Ref


data S = S {
  sDefs :: Map Node Env, -- environment before evaluating a statement
  sGraph :: Graph, -- intraprocedural control flow graph
  sErrs :: [(String, SourcePos)]
}


-- |The environment before evaluation a statement.
getEnv :: Node -> State S Env
getEnv node = do
  s <- get
  case M.lookup node (sDefs s) of
    Just env -> return env
    Nothing -> fail "localTypes: statements out of order"


-- |JavaScript's @typeof@ operator returns one of these strings.
stringToType :: String
             -> Maybe BaseType
stringToType s = case s of
  "string" -> Just TString
  "number" -> Just TNumber
  "function" -> Just TFunction
  "object" -> Just TObject
  "boolean" -> Just TBoolean
  "undefined" -> Just TUndefined
  otherwise -> Nothing

projBaseType :: Ref -> Maybe BaseType
projBaseType (Type (TKnown set)) = case S.toList set of
  [t] -> Just t
  otherwise -> Nothing
projBaseType _ = Nothing


injBaseType :: BaseType -> Ref
injBaseType bt = Type (TKnown (S.singleton bt))


-- |The definition of this function is based on the runtime behavior of
-- the @typeof@ operator.
litToType :: Lit a
          -> Maybe BaseType
litToType lit = case lit of
  StringLit _ s -> Just (TFixedString s)
  RegexpLit _ _ _ _ -> Just TObject
  NumLit _ _ -> Just TNumber
  IntLit _ _ -> Just TNumber
  BoolLit _ _ -> Just TBoolean
  NullLit _ -> Just TObject
  ArrayLit _ _ -> Just TObject
  FuncLit _ _ _ _ -> Just TFunction
  ArgsLit _ _ -> Just TObject
  ObjectLit _ _ -> Just TObject


refineEnv :: Id
          -> BaseType
          -> Env
          -> Env
refineEnv id t env = case M.lookup id env of
  Nothing -> error $ printf "localTypes: %s is unbound" id
  Just t' -> case t' of
    Ref id' -> M.insert id' (Type (TKnown (S.singleton t))) env
    otherwise -> M.insert id (Type (TKnown (S.singleton t))) env


assignEnv :: Id
          -> Ref
          -> Env
          -> State S Env
assignEnv id type_ env = do
  let f (thisId, thisType) 
          | thisId == id = return (thisId, type_)
          | otherwise = case thisType of
              Ref id' | id' == id -> case M.lookup id env of
                Just t -> return (thisId, t)
                Nothing -> fail $ printf "localTypes: %s is unbound" id
              Typeof id' | id' == id -> 
                return (thisId, Type (TKnown (S.singleton TString)))
              otherwise -> return (thisId, thisType)
  lst <- mapM f (M.toList env)
  return (M.fromList lst)

idRoot :: Id
       -> Env
       -> Id
idRoot id env = case M.lookup id env of
  Just (Ref id') -> idRoot id' env
  Just ty -> id
  Nothing -> error $ printf "localTypes: %s is unbound (in idRoot)" id


restrict :: Id
         -> Type
         -> Env
         -> Env
restrict id type_ env = M.insert (idRoot id env) (Type type_) env

remove :: Id
       -> Type
       -> Env
       -> Env
remove id remove env = M.adjust f (idRoot id env)  env
  where  f (Type exist) = case (remove, simpleType exist) of
             (TKnown r, TKnown e) -> 
               Type (TKnown (S.difference e r))
             (TUnk, _) -> error "localTypes: removing TUnk"
             (_, TUnk) -> Type TUnk
             (_, TUnreachable) -> error "localTypes: removing from TUnreachable"
             (TUnreachable, _) -> error "localTypes: removing a TUnreacable"
         f other = error $ "localTypes: root references " ++ show other


unionType :: Type -> Type -> Type
unionType TUnreachable t = t --unionType (TKnown $ S.singleton TUndefined) t
unionType t TUnreachable = t --unionType t (TKnown $ S.singleton TUndefined)
unionType TUnk _ = TUnk
unionType _ TUnk = TUnk
unionType (TKnown ts1) (TKnown ts2) = TKnown (S.union ts1 ts2)


intersectEnv :: Env -> Env -> Env
intersectEnv env1 env2 = M.unionWith f env1 env2
  where f (Type t1) (Type t2) = Type (unionType t1 t2)
        f (Ref id1) (Ref id2) | id1 == id2 = Ref id1
        f (Ref id1) r2 = case M.lookup (idRoot id1 env1) env1 of
          Just root1 -> f root1 r2
          Nothing -> Type TUnk
        f r1 (Ref id2) = case M.lookup (idRoot id2 env2) env2 of
          Just root2 -> f r1 root2
          Nothing -> Type TUnk
        f (Typeof id1) (Typeof id2) 
          | id1 == id2 = Typeof id1
          | otherwise = Type (TKnown (S.singleton TString))
        f (TypeIs id1 t1) (TypeIs id2 t2)   
          | id1 == id2 = TypeIs id1 (unionType t1 t2)
          | otherwise = Type (TKnown (S.singleton TBoolean))
        f (TypeIsNot id1 t1) (TypeIsNot id2 t2)   
          | id1 == id2 = TypeIsNot id1 (unionType t1 t2)
          | otherwise = Type (TKnown (S.singleton TBoolean))
        f _ _ = Type TUnk
        -- other possibilities, e.g. TypeIs + TypeIsNot =~ TypeIs


succs :: Node -> State S [(Node, Maybe (Lit (Int, SourcePos)))]
succs node = do
  state <- get
  return (G.lsuc (sGraph state) node)


stmt :: Env
      -> Node
     -> Stmt (Int, SourcePos)
     -> State S [(Node, Env)]
stmt env node s = do
  succs <-  succs node
  let noop = return (zip (map fst succs) (repeat env)) 
  case s of
    SeqStmt _ _ -> noop
    EmptyStmt _ -> noop
    AssignStmt _ id e -> do
      t <- expr env e
      env <- assignEnv id t env
      return (zip (map fst succs) (repeat env))
    DirectPropAssignStmt _ id field e -> do
      t <- expr env e
      return (zip (map fst succs) (repeat env))
    IndirectPropAssignStmt _ id field e -> do
      t <- expr env e
      return (zip (map fst succs) (repeat env))
    DeleteStmt _ obj field -> noop
    NewStmt _ result constr args -> noop
    CallStmt _ result func args -> noop
    IfStmt _ e _ _ -> do
      t <-  expr env e
      let f (node, Just (BoolLit _ True)) = case unRef t env of
            TypeIs v t -> return (node, restrict v t env)
            TypeIsNot v t -> return (node, remove v t env)
            otherwise -> return (node, env)
          f (node, Just (BoolLit _ False)) = case unRef t env of
            TypeIs v t -> return (node, remove v t env)
            TypeIsNot v t -> return (node, restrict v t env)
            otherwise -> return (node, env)
          f (node, other) = fail "localTypes: invalid successor to IfStmt"
      mapM f succs
    --the conditional in the while acts just like an if
    WhileStmt _ e _ -> do
      t <- expr env e
      let f (node, Just (BoolLit _ True)) = case unRef t env of
            TypeIs v t -> return (node, restrict v t env)
            TypeIsNot v t -> return (node, remove v t env)
            otherwise -> return (node, env)
          f (node, Just (BoolLit _ False)) = case unRef t env of
            TypeIs v t -> return (node, remove v t env)
            TypeIsNot v t -> return (node, restrict v t env)
            otherwise -> return (node, env)
          f (node, other) = fail "localTypes: invalid successor to IfStmt"
      mapM f succs
    ForInStmt _ id e _ -> do
      t <- expr env e
      env <- assignEnv id t env
      return (zip (map fst succs) (repeat env))
    TryStmt _ _ _ _ _ -> noop
    ThrowStmt _ e -> do
      t <- expr env e
      return (zip (map fst succs) (repeat env))
    ReturnStmt _ Nothing -> noop
    ReturnStmt _ (Just e) -> do
      t <- expr env e
      return (zip (map fst succs) (repeat env))
    LabelledStmt _ _ _ -> noop
    BreakStmt _ _ -> noop
    ContinueStmt _ _ -> noop
    SwitchStmt p id cases default_ -> do
      idt' <- expr env (VarRef p id)
      let idt = unRef idt' env
      
      --switch kind of reduces to if:
      let proclit is isnot env lit = do
            occe <- expr env (OpExpr p OpEq [VarRef p id, Lit lit])
            case unRef occe env of
              TypeIs v t -> return (is v t env)
              TypeIsNot v t -> return (isnot v t env)
              otherwise -> return env
          
      let f (node, Just lit) = do
            env' <- proclit restrict remove env lit
            case litToType lit of
              Just t -> do
                --restrict the lit directly as well
                return (node, restrict id (TKnown (S.singleton t)) env')
              _ -> return (node, env')
            
          --default folds over the cases, doing the opposite:
          f (node, Nothing) = do
            env' <- foldM (proclit remove restrict) env (map fst cases)
            return (node, env') -- for default_
      mapM f succs
    EnterStmt _ -> noop
    ExitStmt _ -> noop

expr :: Env
     -> Expr (Int, SourcePos)
     -> State S Ref
expr env e = case e of
  Lit (StringLit _ s) -> return (injBaseType (TFixedString s))
  Lit (RegexpLit _ _ _ _) -> return (injBaseType TObject)
  Lit (NumLit _ _) -> return (injBaseType TNumber)
  Lit (IntLit _ _) -> return (injBaseType TNumber)
  Lit (BoolLit _ _) -> return (injBaseType TBoolean)
  Lit (NullLit _) -> return (Type (TUnk))
  Lit (ArrayLit _ es) -> do
    mapM_ (expr env) es
    return (injBaseType TObject)
  Lit (ArgsLit _ es) -> do
    mapM_ (expr env) es
    return (injBaseType TObject)
  Lit (ObjectLit _ props) -> do
    let es = map (\(_, _, e) -> e) props
    mapM_ (\(_, _, e) -> expr env e) props
    return (injBaseType TObject)
  Lit (FuncLit _ _ _ _) -> return (injBaseType TFunction)
  VarRef _ id -> return (Ref id)
  DotRef _ obj field -> do
    _ <- expr env obj
    return (Type TUnk) -- we could do better here
  BracketRef _ e1 e2 -> do
    _ <- expr env e1
    _ <- expr env e2
    return (Type TUnk) -- we could do better here
  OpExpr _ op es -> do
    let lhs = es !! 0
    let rhs = es !! 1 -- if op does not have an rhs, reducing this will fail
    let comparison = do
          t1 <- expr env lhs
          t2 <- expr env rhs
          return (injBaseType TBoolean)
    let equality' t1 t2 = case (unRef t1 env, unRef t2 env) of
          (Typeof id, projBaseType -> Just (TFixedString s)) -> 
            case stringToType s of
              Nothing -> return (injBaseType TBoolean)
              Just localType -> 
                return (TypeIs id (TKnown (S.singleton localType)))
          (projBaseType -> Just (TFixedString _), Typeof _) ->
            equality' t2 t1
          otherwise -> return (injBaseType TBoolean)
    let equality = do
          t1 <- expr env lhs
          t2 <- expr env rhs
          equality' t1 t2
    let inequality = do
          t <- equality
          case t of
            TypeIs id t -> return (TypeIsNot id t)
            otherwise -> return (Type TUnk)
    let arithmetic = do
          expr env lhs
          expr env rhs
          return (injBaseType TNumber)           
    case op of
      PrefixTypeof -> do
        t <- expr env lhs
        case t of
          Ref id -> return (Typeof id)
          otherwise -> return (Type TUnk)
      OpEq -> equality
      OpStrictEq -> equality
      OpNEq -> inequality
      OpStrictNEq -> inequality
      OpLT -> comparison
      OpLEq -> comparison
      OpGT -> comparison
      OpGEq -> comparison
      OpIn -> comparison
      OpInstanceof -> comparison
      PrefixLNot -> do
        t <- expr env lhs
        case t of
          TypeIs id t' -> return (TypeIsNot id t')
          TypeIsNot id t' -> return (TypeIs id t')
          otherwise -> return (injBaseType TBoolean)
      PrefixBNot -> do
        t <- expr env lhs
        return (injBaseType TNumber)
      PrefixMinus -> do
        t <- expr env lhs
        return (injBaseType TNumber)
      PrefixVoid -> do
        t <- expr env lhs
        return (injBaseType TUndefined)
      OpMul -> arithmetic
      OpDiv -> arithmetic
      OpMod -> arithmetic
      OpSub -> arithmetic
      OpLShift -> arithmetic
      OpSpRShift -> arithmetic
      OpZfRShift -> arithmetic
      OpBAnd -> arithmetic
      OpBXor -> arithmetic
      OpBOr -> arithmetic
      OpAdd -> do
        t1 <- expr env lhs
        t2 <- expr env rhs
        case (unRef t1 env, unRef t2 env) of
          (projBaseType -> Just TString, _) -> return (injBaseType TString)
          (_, projBaseType -> Just TString) -> return (injBaseType TString)
          (projBaseType -> Just TNumber, projBaseType -> Just TNumber) ->
            return (injBaseType TNumber)
          otherwise -> return (Type TUnk)


stmtFromNode :: Graph -> Node -> Stmt (Int, SourcePos)
stmtFromNode gr node = case G.lab gr node of
  Just s -> s
  Nothing -> error $ printf 
    "localTypes: %s is not a node" (show node)


body :: Env -> State S ()
body initEnv = do
  state <- get
  let gr = sGraph state
  let (enterNode, _) = G.nodeRange gr
  let setEnv (node, env) = do
        s <- get
        let defs = sDefs s
        case M.lookup node defs of
          Nothing -> do
            put $ s { sDefs = M.insert node env defs }
            return True
          Just env' -> case env == env' of
            True -> return False
            False -> do put $ s { sDefs = M.insert node
                                                  (intersectEnv env env')
                                                  defs }
                        return True

  let getEnv node = do
        s <- get
        case M.lookup node (sDefs s) of
          Just env -> return env
          Nothing -> fail "getEnv failure"

  let work :: [(Node, Env)] -> State S ()
      work [] = return ()
      work ((node, env):rest) = do
        r <- setEnv (node, env)
        case r of
          True -> do
            env <- getEnv node
            succs <- stmt env node (stmtFromNode gr node)
            work (rest ++ succs)
          False -> work rest


  work [(enterNode, initEnv)]


simpleBaseType :: BaseType -> BaseType
simpleBaseType (TFixedString _) = TString
simpleBaseType t = t


simpleType :: Type -> Type
simpleType (TKnown ts) = TKnown (S.map simpleBaseType ts)
simpleType TUnk = TUnk
simpleType TUnreachable = TUnreachable

unRef :: Ref -> Env -> Ref
unRef (Ref id) env = case M.lookup id env of
  Just r -> unRef r env
  Nothing -> error "localTypes: unbound ref"
unRef r _ = r

flattenEnv :: Map Id Ref -> Map Id Type
flattenEnv env = M.map f env 
  where f (Type t) = simpleType t
        f (Ref id) = case M.lookup (idRoot id env) env of
          Just (Ref id') -> error $ printf "localTypes: %s -> %s" id id'
          Just r -> f r
          Nothing -> error $ printf "localTypes: %s is unbound at exit" id
        f (Typeof _) = TKnown (S.singleton TString)
        f (TypeIs _ _) = TKnown (S.singleton TBoolean)
        f (TypeIsNot _ _) = TKnown (S.singleton TBoolean)


localTypes :: Graph -- ^intraprocedural control flow graph of a function
           -> Map Id Type -- ^environment of the function
           -> Map Node (Map Id Type) -- ^environment at each statement
localTypes gr env = M.map flattenEnv (sDefs (execState (body enterEnv) s))
  where enterEnv = M.map Type env
        (enterNode, _) = G.nodeRange gr
        s = S M.empty gr []

localRefs :: Graph -- ^intraprocedural control flow graph of a function
           -> Map Id Type -- ^environment of the function
           -> Map Node (Map Id Ref) -- ^environment at each statement
localRefs gr env = sDefs (execState (body enterEnv) s)
  where enterEnv = M.map Type env
        (enterNode, _) = G.nodeRange gr
        s = S M.empty gr []

prettyRefEnv :: Map Id Ref -> PP.Doc
prettyRefEnv env = PP.cat (PP.punctuate PP.comma (map f $ M.toList env))
  where f (id, t) = PP.text $ printf "%s = %s" id (show t)

prettyEnv :: Map Id Type -> PP.Doc
prettyEnv env = PP.cat (PP.punctuate PP.comma (map f $ M.toList env))
  where f (id, t) = PP.text $ printf "%s = %s" id (show t)
