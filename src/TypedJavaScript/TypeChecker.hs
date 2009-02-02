-- |
-- Maintainer: arjun@cs.brown.edu
--
-- Determine the environment of a JavaScript function.
module TypedJavaScript.TypeChecker
  (
    typeCheckStmt,
    typeOfExpr
  ) where

import Data.Generics
import Data.List (foldl')

import Text.ParserCombinators.Parsec(SourcePos)
import Text.ParserCombinators.Parsec.Pos
import TypedJavaScript.Syntax
import TypedJavaScript.Environment

-- ----------------------------------------------------------------------------
type Env = [(Id SourcePos, Type SourcePos)]

lookupEnv :: Env -> String -> Type SourcePos
lookupEnv [] s = error "lookupEnv: empty environment"
lookupEnv ((Id pos idname,t):rest) s = 
  if idname == s
    then t
    else lookupEnv rest s

--TODO: deal with TApp, add syntax for defining them , etc.

--resolve a type by reducing TId and TExpr to other types 
--if we have a TId, look it up until we get to one of the base types
resolveType :: Env -> Env -> (Type SourcePos) -> (Type SourcePos)
resolveType vars types t = case t of
  TId a id -> case id of
    "string" -> t
    "double" -> t
    "int" -> t
    "bool" -> t
    "undefined" -> t
    _ -> resolveType vars types $ lookupEnv types id
  TExpr a expr -> resolveType vars types $ typeOfExpr vars types expr
  other -> other
  
-- we need two environments - one mapping variable id's to their types, and
-- one matching type id's to their type. types gets extended with external and type statements.
-- this function reduces everything to TObject, TFunc, or a base-case TId.
typeOfExpr :: Env -> Env -> (Expression SourcePos) -> Type SourcePos
typeOfExpr vars types expr = case expr of
  StringLit a _      -> TId a "string"
  RegexpLit a _ _ _  -> TId a "Regex"
  NumLit a _         -> TId a "double"
  IntLit a _         -> TId a "int"
  BoolLit a _        -> TId a "bool"
  NullLit a          -> TId a "undefined"  --TODO: should null just be undefined?

  ArrayLit a exprs   -> error "NYI"
  ObjectLit a props  -> error "NYI"

  ThisRef a          -> resolveType vars types $ lookupEnv vars "this"
  VarRef a (Id _ s)  -> resolveType vars types $ lookupEnv vars s

  DotRef a expr id   -> error "NYI"
  BracketRef a xc xk -> error "NYI"
  NewExpr a xcon xvars -> error "NYI"
  PostfixExpr a op x -> error "NYI"
  PrefixExpr a op x -> error "NYI"
  InfixExpr a op l r -> error "NYI"
  CondExpr a c t e -> error "NYI"
  AssignExpr a op lhs rhs -> error "NYI"

  ParenExpr a x -> typeOfExpr vars types expr
  ListExpr a exprs -> typeOfExpr vars types $ last exprs
  
  CallExpr a funcexpr argexprs -> error "NYI"
  FuncExpr a argnames functype bodystmt -> 
    case resolveType vars types functype of
      TFunc a thistype reqargs optargs vararg rettype -> error "NYI"
      _ -> error "Function must have a function type."

{-      
              TExpr a (Expression a) | TObject a [(Id a, Type a)]
              | TFunc a (Maybe (Type a)) {- type of this -} 
                        [Type a] {- required args -} 
                        [Type a] {- optional args -}
                        (Maybe (Type a)) {- optional var arg -}
                        (Type a) {- ret type -}
              | TId a String -- an Id defined through a 'type' statement
              | TApp a (Type a) [Type a]
 -}

typeCheckStmt :: Env -> Env -> (Statement SourcePos) -> Bool
typeCheckStmt vars types stmt = case stmt of 
  BlockStmt pos stmts -> all (typeCheckStmt vars types) stmts
  EmptyStmt pos -> True
  -- TODO: figure out how to throw proper errors
  ExprStmt  pos expr -> do
    let _ = typeOfExpr vars types expr
    True
  IfStmt pos c t e -> 
     case typeOfExpr vars types c of
       TId _ "bool" -> all (typeCheckStmt vars types) [t, e]
       _ -> error "test expression must be a boolean"
  IfSingleStmt pos c t ->
     case typeOfExpr vars types c of
       TId _ "bool" -> (typeCheckStmt vars types t)
       _ -> error "test expression must be a boolean"
  SwitchStmt pos expr clauses -> do
     let _ = typeOfExpr vars types expr 
     all (\c -> case c of 
                   CaseClause pos expr stmts -> do
                       let _ = typeOfExpr vars types expr
                       all (typeCheckStmt vars types) stmts
                   CaseDefault pos stmts -> all (typeCheckStmt vars types) stmts)
         clauses
  WhileStmt pos expr statement -> do
     let _ = typeOfExpr vars types expr
     typeCheckStmt vars types statement
  DoWhileStmt pos statement expr -> do
     let res = typeCheckStmt vars types statement
     let _ = typeOfExpr vars types expr
     res
  BreakStmt _ _ -> True
  ContinueStmt _ _ -> True
  LabelledStmt _ _ stmt -> typeCheckStmt vars types stmt
  --ForInStmt
{-
data Statement a
  = BlockStmt a [Statement a]
  | EmptyStmt a
  | ExprStmt a (Expression a)
  | IfStmt a (Expression a) (Statement a) (Statement a)
  | IfSingleStmt a (Expression a) (Statement a)
  | SwitchStmt a (Expression a) [CaseClause a]
  | WhileStmt a (Expression a) (Statement a)
  | DoWhileStmt a (Statement a) (Expression a)
  | BreakStmt a (Maybe (Id a))
  | ContinueStmt a (Maybe (Id a))
  | LabelledStmt a (Id a) (Statement a)
  | ForInStmt a (ForInInit a) (Expression a) (Statement a)
  | ForStmt a (ForInit a)        
              (Maybe (Expression a)) -- increment
              (Maybe (Expression a)) -- test
              (Statement a)          -- body
  | TryStmt a (Statement a) {-body-} [CatchClause a] {-catches-}
      (Maybe (Statement a)) {-finally-}
  | ThrowStmt a (Expression a)
  | ReturnStmt a (Maybe (Expression a))
  -- | WithStmt a (Expression a) (Statement a)
  | VarDeclStmt a [VarDecl a]
  -- FunctionStatements turn into expressions with an assignment. 
  -- TODO: add generics to functions/constructors?
  -- | FunctionStmt a (Id a) {-name-} [(Id a, Type a)] {-args-} (Maybe (Type a)) {-ret type-}  (Statement a) {-body-}
  | ConstructorStmt a (Id a) {-name-} 
                      [(Id a, Type a)] {- required args -}
                      [(Id a, Type a)] {- optional args -}
                      (Maybe (Id a, Type a)) {- optional var arg -}
                      (Statement a) {-body-}
  | TypeStmt a (Id a) (Type a) -- e.g. type Point :: {x :: int, y :: int};
  
  -}

typeCheckStmts :: Env -> Env -> [(Statement SourcePos)] -> Bool
typeCheckStmts vars types stmts = typeCheckStmt vars types $ BlockStmt (initialPos "[]") stmts

