module BrownPLT.TypedJS.TypeCheck
  ( typeCheck
  , typeCheckExpr
  ) where

import BrownPLT.TypedJS.FreeVars
import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.LocalVars (localVars, Binding)
import BrownPLT.TypedJS.RuntimeAnnotations (runtimeAnnotations)
import BrownPLT.TypedJS.TypeDefinitions
import BrownPLT.TypedJS.TypeTheory
import TypedJavaScript.PrettyPrint
import TypedJavaScript.Syntax
import qualified Data.Map as M


data S = S {
  stateErrors :: [(SourcePos, String)]
}

data TypeCheck a = TypeCheck { runTypeCheck :: S  -> (S, Either String a) }

instance Monad TypeCheck where

  return a = TypeCheck $ \s -> (s, Right a)

  fail str = TypeCheck $ \s -> (s, Left str)

  (TypeCheck f) >>= g = TypeCheck $ \s -> case f s of
    (s', Left str) -> (s', Left str)
    (s', Right a) -> runTypeCheck (g a) s'


getState :: TypeCheck S
getState = TypeCheck $ \s -> (s, Right s)


putState :: S -> TypeCheck ()
putState s = TypeCheck $ \_ -> (s, Right ())
  

typeError :: SourcePos
          -> String
          -> TypeCheck ()
typeError loc msg = do
  s <- getState
  putState $ s { stateErrors = (loc, msg):(stateErrors s) }

fatalTypeError :: SourcePos -> String -> TypeCheck a
fatalTypeError p msg = fail (printf "%s: %s" (show p) msg)


data Env = Env Int (Map String (Type, Int))


emptyEnv :: Env
emptyEnv = Env 0 M.empty

domEnv :: Env -> [String]
domEnv (Env _ dict) = M.keys dict

lookupEnv :: Monad m
          => SourcePos 
          -> Env
          -> String
          -> m Type
lookupEnv loc env x = do
  (t, n) <- lookupScopeEnv loc env x
  return t


lookupScopeEnv :: Monad m
               => SourcePos
               -> Env
               -> String
               -> m (Type, Int)
lookupScopeEnv loc (Env _ dict) x = case M.lookup x dict of
  Nothing -> fail $ printf "unbound identifier %s at %s" x (show loc)
  Just (t, n) -> return (t, n)


scopeEnv :: Env -> Int
scopeEnv (Env n _) = n


extendEnv :: Env -> String -> Type -> Env
extendEnv (Env n dict) x t = Env n (M.insert x (t, n) dict)


extendsEnv :: Env -> [(String, Type)] -> Env
extendsEnv env binds = foldr (\(x, t) env -> extendEnv env x t) env binds


-- runtimeEnv :: Env -> Map String RuntimeTypeInfo
runtimeEnv (Env _ dict) = M.map (runtime.fst) dict


nestEnv :: Env -> Env
nestEnv (Env n dict) = Env (n + 1) dict


ok :: TypeCheck ()
ok = return ()


fieldType :: String -> [Field] -> Maybe (Bool, Type)
fieldType _ [] = Nothing
fieldType x ((y, ro, t):fs) | x == y = Just (ro, t)
                            | x > y = fieldType x fs
                            | otherwise = Nothing


-- |Calculates the type of a local variable that does not have a type
-- type annotation.  Extends the environment with the type of the variable.
-- Expects the environment to contain the preceding local variables.
--
-- Fold this function over the result of @localVars@.  Although local variables
-- are visible to each other, the only way to have recursive definitions is
-- with functions.  However, functions have explicit type annotations, even
-- if the variable itself does not have one.  Anything else counts as a define-
-- before-use error.
calcType :: Env
         -> Binding
         -> TypeCheck Env
calcType env (id, Right t) = return (extendEnv env id (canonize t))
calcType env (id, Left (FuncExpr _ _ t _)) = return (extendEnv env id t)
calcType env (id, Left e) = do
  t <- expr env e
  return (extendEnv env id t)


field :: Env
      -> (Prop SourcePos, Maybe Type, Expression SourcePos)
      -> TypeCheck Field
field env f = case f of
  (PropId p (Id _ x), Nothing, e) -> do
    t <- expr env e
    return (x, False, t) -- fields are mutable by default
  (PropId p (Id _ x), Just s, e) -> do
    t <- expr env e
    case isSubtype t s of
      True -> return (x, False, s)
      False -> do
        typeError p $ printf 
          "field %s :: %s, but the expression has type %s"
          x (renderType s) (renderType t)
        return (x, False, s)
          
numericOp :: SourcePos -> Expression SourcePos
          -> Type -> Type -> Bool -> Bool -> TypeCheck Type
numericOp loc e lhs rhs requireInts returnDouble = do
  let result = return $ case returnDouble of
                 True -> doubleType
                 False -> if isSubtype lhs intType then rhs else lhs
  case requireInts of
    True -> do
      unless (isSubtype lhs intType && isSubtype rhs intType) $
        typeError loc $ printf 
          "operator expects Int arguments, given %s and %s in expression %s" 
          (renderType lhs) (renderType rhs) (renderExpr e)
      result
    False -> do
      unless (isSubtype lhs doubleType && isSubtype rhs doubleType) $
        typeError loc $ printf 
          "operator expects double/int arguments, given %s and %s" 
          (renderType lhs) (renderType rhs) (renderExpr e)
      result

expr :: Env 
     -> Expression SourcePos 
     -> TypeCheck Type
expr env e = case e of
  StringLit _ _ -> return stringType
  RegexpLit _ _ _ _ -> fail "RegexpLit NYI"
  NumLit _ _ -> return doubleType
  IntLit _ _ -> return intType
  BoolLit _ _ -> return boolType
  NullLit _ -> fail "NullLit NYI"
  ThisRef p -> lookupEnv p env "this"
  VarRef p (Id _ x) -> lookupEnv p env x
  PostfixExpr p op e -> fail "PostfixExpr NYI"
  PrefixExpr p op e -> do
    t <- expr env e
    case op of
      PrefixLNot -> return boolType
      PrefixBNot | isSubtype t doubleType -> return t
      PrefixPlus | isSubtype t doubleType -> return t
      PrefixMinus | isSubtype t doubleType -> return t
      PrefixTypeof -> return stringType
      PrefixVoid -> fail "PrefixVoid NYI"
      PrefixDelete -> fail "PrefioxDelete NYI"
      otherwise -> fail $ printf "%s applied to an expression of type %s"
                                        (show op) (renderType t)
  InfixExpr p op e1 e2 -> do
    lhs <- expr env e1
    rhs <- expr env e2
    let cmp = do
          unless ((isSubtype lhs stringType && isSubtype rhs stringType) ||
                  (isSubtype lhs doubleType && isSubtype rhs doubleType)) $
            typeError p $ printf "%s may only be applied to numbers and strings"
                                 (show op)
          return boolType
    case op of
      OpLT -> cmp
      OpLEq -> cmp
      OpGT -> cmp
      OpGEq -> cmp
      OpIn -> fail "OpIn NYI"
      OpInstanceof -> return boolType
      OpEq -> return boolType
      OpNEq -> return boolType
      OpStrictEq -> return boolType
      OpStrictNEq -> return boolType
      OpMul -> numericOp p e lhs rhs False False
      OpDiv -> numericOp p e lhs rhs False True
      OpMod -> numericOp p e lhs rhs False True
      OpSub -> numericOp p e lhs rhs False False
      OpLShift -> numericOp p e lhs rhs True False
      OpSpRShift -> numericOp p e lhs rhs True False
      OpZfRShift -> numericOp p e lhs rhs True False
      OpBAnd -> numericOp p e lhs rhs True False
      OpBXor -> numericOp p e lhs rhs True False
      OpBOr -> numericOp p e lhs rhs True False
      OpAdd | isSubtype lhs stringType -> return stringType
            | isSubtype rhs stringType -> return stringType
            | otherwise -> numericOp p e lhs rhs False False
      OpLAnd -> return (canonicalUnion rhs boolType)
      OpLOr -> return (canonicalUnion lhs rhs)
  CondExpr p e1 e2 e3 -> do
    t1 <- expr env e1
    t2 <- expr env e2
    t3 <- expr env e3
    return (canonicalUnion t2 t3)
  AssignExpr p OpAssign lhs rhs -> do
    t <- expr env rhs
    case lhs of
      LVar p2 x -> do
        (s, n) <- lookupScopeEnv p2 env x
        case n < scopeEnv env of
          -- x is a variable in an enclosing scope.
          True -> fail "assinging to enclosing scopes NYI"
          -- x is a local variable.  The local scope may make assumptions about
          -- its runtime type.
          False | isSubtype t s -> return t
                | otherwise -> do
                    typeError p $ printf
                      "error assigning to local variable of type %s, given an \
                      \expression of type %s" (renderType s) (renderType t)
                    return s
      LDot p2 obj f -> do
        tObj <- expr env obj
        case tObj of
          TObject brand fields -> case fieldType f fields of
            Just (True, s) -> do
              typeError p2 $ printf "the field %s is readonly" f
              return s       
            Nothing -> do
              typeError p2 $ printf "object does not have the field %s" f
              return t
            Just (False, s) 
              | s == t -> return s
              | otherwise -> do
                  typeError p2 $ printf
                    "the field %s :: %s, but the expression has the type %s"
                    f (renderType s) (renderType t)
                  return s
  ParenExpr _ e -> expr env e
  ListExpr p [] -> catastrophe p "empty ListExpr"
  ListExpr p es -> 
    foldM (\_ e -> expr env e) undefined es -- type of the last expression
  ObjectLit p fields -> do
    ts <- mapM (field env) fields
    -- TODO: ensure fields are unique
    return (canonize (TObject "Object" ts))
  CallExpr p f ts args -> do
    f_t <- expr env f
    args_t <- mapM (expr env) args
    case f_t of
      TArrow thisType (ArgType argTypes optArgType) resultType -> do
        unless (length args == length argTypes) $ 
          typeError p "argument count mismatch"
        unless (all (uncurry isSubtype) (zip args_t argTypes)) $
          typeError p "argument type mismatch"
        return resultType
      otherwise -> do
        typeError p $ printf "expected a function; expression has type %s"
          (renderType f_t)
        fail "type error"
  FuncExpr p args t body -> case canonize t of
    TArrow thisType (ArgType argTypes optArgType) resultType -> do
      unless (length args == length (nub $ map unId args)) $
        fatalTypeError p "function argument names must be unique"

      unless (length args == length argTypes) $
        fail $ "argument count mismatch at " ++ show p
      let envWithArgs = extendsEnv (nestEnv env) (zip (map unId args) argTypes)
      -- TODO: Check is allPathsReturn.  If not, it must be that
      -- undefType <: returnType.
      -- When we get to constructors, omit this test but use stmt with
      -- returnType = Nothing
      case runtimeAnnotations (runtimeEnv envWithArgs) body of
        Left s -> catastrophe p s
        Right body -> do
          let localBinds = localVars body
          let newNames = map unId args ++ (map fst localBinds)
          unless (length newNames == length (nub newNames)) $
            fail $ "duplicate names in a scope at " ++ show p
          envWithLocals <- foldM calcType envWithArgs localBinds
          stmt envWithLocals (Just resultType) body
          return (canonize t)
    -- annotation on the function is not a function type
    otherwise -> do
      typeError p $ printf "expected a function type, received %s" 
                           (renderType t)
      return t
  AnnotatedVarRef p rt x -> do
    s <- lookupEnv p env x
    case static rt s of
      Just t -> return t
      Nothing -> catastrophe p $ 
        printf "%s :: %s is inconsistent with the runtime type %s" 
               x (renderType s) (show rt)




stmt :: Env
     -> Maybe Type -- ^ return type
     -> Statement SourcePos
     -> TypeCheck ()
stmt env returnType s = case s of
  BlockStmt _ ss -> mapM_ (stmt env returnType) ss
  EmptyStmt _ -> ok
  ExprStmt _ e -> expr env e >> ok
  IfStmt _ e s1 s2 -> do
    expr env e -- we permit non-boolean tests
    stmt env returnType s1
    stmt env returnType s2
  IfSingleStmt _ e s -> do
    expr env e -- we permit non-boolean tests
    stmt env returnType s
  SwitchStmt _ e cases -> do
    expr env e
    let case_ (CaseClause _ e ss) = do
          expr env e
          mapM_ (stmt env returnType) ss
        case_ (CaseDefault _ ss) =
          mapM_ (stmt env returnType) ss
    mapM_ case_ cases
  WhileStmt _ e s -> do
    expr env e
    stmt env returnType s
  DoWhileStmt _ s e -> do
    stmt env returnType s
    expr env e
    ok
  BreakStmt _ _ -> ok
  ContinueStmt _ _ -> ok
  LabelledStmt _ _ s -> stmt env returnType s
  ForInStmt _ init e s -> fail "ForInStmt NYI"
  ForStmt _ init test incr s -> fail "ForStmt NYI"
  TryStmt _ body catches finally -> fail "TryStmt NYI"
  ThrowStmt _ e -> expr env e >> ok
  ReturnStmt p ret -> case returnType of
    Nothing -> typeError p $ printf "return used in a constructor or at the \
                                    \top level"
    Just returnType -> case ret of
      Nothing | isSubtype undefType returnType -> ok
              | otherwise -> typeError p $ printf 
                               "empty return, expected %s" 
                               (renderType returnType)
      Just e -> do
        t <- expr env e
        case isSubtype t returnType of
          True -> ok
          False -> typeError p $ printf "statement returns %s, expected %s"
                     (renderType t) (renderType returnType)
  VarDeclStmt p decls -> do
    let decl (VarDecl _ (Id _ x) t) = case isSubtype undefType (canonize t) of
          True -> ok
          False -> do typeError p "uninitalized variable declarations must \
                                  \have type undefined"
                      ok
        decl (VarDeclExpr _ (Id _ x) (Just t) e) = do
          s <- expr env e
          case isSubtype s (canonize t) of
            True -> ok
            False -> do typeError p $ printf 
                          "expression has type %s, expected a subtype of %s"
                          (renderType s) (renderType t)
        -- calcType has already called 'expr' on 'e' below
        decl (VarDeclExpr _ (Id _ x) Nothing e) = ok
    mapM_ decl decls


-- |This code should be almost identical to the code for function bodies.
topLevel :: Env -> [Statement SourcePos] -> TypeCheck ()
topLevel globals body = case freeVars (domEnv globals) body of
  [] -> case runtimeAnnotations (runtimeEnv globals) (BlockStmt noPos body) of
    Left s -> catastrophe noPos s
    Right body -> do
      let localBinds = localVars body
      let newNames = (domEnv globals) ++ (map fst localBinds)
      unless (length newNames == length (nub newNames)) $
        fail $ "duplicate names at top level at "
      envWithGlobals <- foldM calcType globals localBinds
      stmt envWithGlobals Nothing body
  freeVars -> fatalTypeError noPos $ printf "Undeclared identifiers: %s"
    (show freeVars)


typeCheck :: [Statement SourcePos] -> Either String ()
typeCheck body = case runTypeCheck (topLevel emptyEnv body) (S []) of
  (S [], Right ()) -> return ()
  (S errs, Left err) -> Left (show errs ++ "\n\n" ++ err)
  (S errs, _) -> Left (show errs)


typeCheckExpr :: Expression SourcePos -> Either String Type
typeCheckExpr e = case freeVars [] [ExprStmt noPos e] of
  [] -> do
    body <- runtimeAnnotations M.empty (ExprStmt noPos e)
    case body of
      ExprStmt _ e -> case runTypeCheck (expr emptyEnv e) (S []) of
        (S [], Right t) -> return t
        (S errs, Left err) -> fail (show errs ++ "\n\n" ++ err)
        (S errs, _) -> fail (show errs)
      otherwise -> error "typeCheckExpr: expression shape error"
  freeVars -> fail $ printf "unbound identifiers: %s" (show freeVars)
