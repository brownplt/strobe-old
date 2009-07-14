module BrownPLT.TypedJS.TypeCheck
  ( typeCheck
  ) where

import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.LocalVars (localVars, Binding)
import BrownPLT.TypedJS.RuntimeAnnotations (runtimeAnnotations)
import BrownPLT.TypedJS.TypeTheory
import TypedJavaScript.PrettyPrint
import TypedJavaScript.Syntax
import Control.Monad.State.Strict
import qualified Data.Map as M


data S = S {
  stateErrors :: [(SourcePos, String)]
}


type TypeCheck a = State S a


typeError :: SourcePos
          -> String
          -> TypeCheck ()
typeError loc msg = do
  s <- get
  put $ s { stateErrors = (loc, msg):(stateErrors s) }


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
calcType env (id, Right t) = return (extendEnv env id t)
calcType env (id, Left (FuncExpr _ _ t _)) = return (extendEnv env id t)
calcType env (id, Left e) = do
  t <- expr env e
  return (extendEnv env id t)


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
      PrefixLNot | isSubtype t boolType -> return boolType
      PrefixBNot | isSubtype t doubleType -> return t
      PrefixPlus | isSubtype t doubleType -> return t
      PrefixMinus | isSubtype t doubleType -> return t
      PrefixTypeof -> return stringType
      PrefixVoid -> fail "PrefixVoid NYI"
      PrefixDelete -> fail "PrefioxDelete NYI"
      otherwise -> fail $ printf "%s applied to an expression of type %s"
                                        (show op) (renderType t)
  InfixExpr p op e1 e2 -> do
    t1 <- expr env e1
    t2 <- expr env e2
    case op of
      OpEq -> return boolType
      otherwise -> fail $ show op ++ " NYI"
  CondExpr p e1 e2 e3 -> fail "condExpr NYI"
  AssignExpr p OpAssign lhs rhs -> do
    t <- expr env e
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
  ParenExpr _ e -> expr env e
  ListExpr p [] -> catastrophe p "empty ListExpr"
  ListExpr p es -> 
    foldM (\_ e -> expr env e) 
          undefined
          es -- type of the last expression
  CallExpr p f ts args -> fail "CallExpr NYI"
  FuncExpr p args t body -> case t of
    TArrow thisType (ArgType argTypes optArgType) resultType -> do
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
          return t
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
    let decl (VarDecl _ (Id _ x) t) = case isSubtype undefType t of
          True -> ok
          False -> do typeError p "uninitalized variable declarations must \
                                  \have type undefined"
                      ok
        decl (VarDeclExpr _ (Id _ x) (Just t) e) = do
          s <- expr env e
          case isSubtype s t of
            True -> ok
            False -> do typeError p $ printf 
                          "expression has type %s, expected a subtype of %s"
                          (renderType s) (renderType t)
        -- calcType has already called 'expr' on 'e' below
        decl (VarDeclExpr _ (Id _ x) Nothing e) = ok
    mapM_ decl decls


-- |This code should be almost identical to the code for function bodies.
topLevel :: Env -> [Statement SourcePos] -> TypeCheck ()
topLevel globals body = do
  case runtimeAnnotations (runtimeEnv globals) (BlockStmt noPos body) of
    Left s -> catastrophe noPos s
    Right body -> do
      let localBinds = localVars body
      let newNames = (domEnv globals) ++ (map fst localBinds)
      unless (length newNames == length (nub newNames)) $
        fail $ "duplicate names at top level at "
      envWithGlobals <- foldM calcType globals localBinds
      stmt envWithGlobals Nothing body


typeCheck :: [Statement SourcePos] -> IO ()
typeCheck body = case execState (topLevel emptyEnv body) (S []) of
  S [] -> return ()
  S errs -> mapM_ (putStrLn.show) errs
  
