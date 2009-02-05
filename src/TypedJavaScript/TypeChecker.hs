module TypedJavaScript.TypeChecker
  ( typeOfExpr
  , resolveType
  , typeCheckStmt
  , typeCheckStmts
  , Env
  , coreTypeEnv
  , coreVarEnv
  ) where

import Data.Generics
import Data.List (foldl')
import qualified Data.Map as M
import Data.Map(Map, (!))
import Control.Monad(liftM)

import Text.ParserCombinators.Parsec(SourcePos)
import Text.ParserCombinators.Parsec.Pos
import TypedJavaScript.Syntax
import TypedJavaScript.Environment

-- ----------------------------------------------------------------------------
-- TODO: use Data.Map
--       get rid of resolveType
--       "string" -> TApp (TID "String") []
type Env = Map String (Type SourcePos)

resolveType :: (Monad m) => Env -> Env -> (Type SourcePos) -> m (Type SourcePos)
resolveType vars types t = case t of
  TId _ s -> return $ types ! s
  -- TExpr _ x -> typeOfExpr vars types x
  _ -> return t

corePos = initialPos "core"

-- TODO: figure out what to do with global.
globalObjectType = TObject corePos []

coreTypeEnv :: Env
coreTypeEnv = M.fromList $ (map (\s -> (s, (TApp corePos (TId corePos s) [])))
                                ["string", "double", "int", "bool", "undefined"]) ++
                           [("@global", globalObjectType)]
coreVarEnv :: Env
coreVarEnv = M.fromList [("this", coreTypeEnv ! "@global")]

--TODO: deal with TApp, add syntax for defining them , etc.

-- TODO: Allow ! to work on anything, or just booleans?
-- Same goes for -, +, etc. 
{- alternative:
   case t of
      (TApp _ (TId _ "int") []) -> return t
      (TApp _ (TId _ "double") []) -> return t
      _ -> fail $ "Expected int or double, got: " ++ (show xtype) -}

-- in pJS, anything can be used in a number and bool context without anything crashing.
numberContext :: (Monad m) => Env -> Env -> (Type SourcePos) -> m (Type SourcePos)
numberContext vars types t
   | t == (types ! "int") = return t
   | otherwise            = return $ types ! "double"

--TODO: this always returns the bool type. not sure how to notate that in the type sig.    
boolContext :: (Monad m) => Env -> Env -> (Type SourcePos) -> m (Type SourcePos)
boolContext vars types t = return $ types ! "bool"

-- we need two environments - one mapping variable id's to their types, and
-- one matching type id's to their type. types gets extended with external and type statements.
-- this function reduces everything to TObject, TFunc, or a base-case TId.
typeOfExpr :: (Monad m) => Env -> Env -> (Expression SourcePos) -> m (Type SourcePos)
typeOfExpr vars types expr = case expr of
  StringLit a _      -> return $ types ! "string"
  RegexpLit a _ _ _  -> return $ types ! "RegExp"
  NumLit a _         -> return $ types ! "double"
  IntLit a _         -> return $ types ! "int"
  BoolLit a _        -> return $ types ! "bool"
  NullLit a          -> return $ types ! "undefined"  --TODO: should null just be undefined?

  ArrayLit a exprs   -> fail "NYI"
  ObjectLit a props  -> fail "NYI"

-- [(Prop a, Maybe (Type a), Expression a)]
  ThisRef a          -> return $ vars ! "this"
  VarRef a (Id _ s)  -> return $ vars ! s

  DotRef a expr id   -> fail "NYI"
  BracketRef a xc xk -> fail "NYI"
  NewExpr a xcon xvars -> fail "NYI"
  
{- February 2009 (show all)  	
next >
Sun 	Mon 	Tue 	Wed 	Thu 	Fri
data InfixOp = OpLT | OpLEq | OpGT | OpGEq  | OpIn  | OpInstanceof | OpEq | OpNEq
             | OpStrictEq | OpStrictNEq | OpLAnd | OpLOr 
             | OpMul | OpDiv | OpMod  | OpSub | OpLShift | OpSpRShift
             | OpZfRShift | OpBAnd | OpBXor | OpBOr | OpAdd
    deriving (Show,Data,Typeable,Eq,Ord,Enum)

data AssignOp = OpAssign | OpAssignAdd | OpAssignSub | OpAssignMul | OpAssignDiv
  | OpAssignMod | OpAssignLShift | OpAssignSpRShift | OpAssignZfRShift
  | OpAssignBAnd | OpAssignBXor | OpAssignBOr
  deriving (Show,Data,Typeable,Eq,Ord)

data PrefixOp = PrefixInc | PrefixDec | PrefixLNot | PrefixBNot | PrefixPlus
  | PrefixMinus | PrefixTypeof -- | PrefixVoid 
  | PrefixDelete
  deriving (Show,Data,Typeable,Eq,Ord)
  
data PostfixOp 
  = PostfixInc | PostfixDec
  deriving (Show,Data,Typeable,Eq,Ord) 
-}
  
  PostfixExpr a op x -> do
    xtype <- typeOfExpr vars types x
    numberContext vars types xtype
  
  PrefixExpr a op x -> do
    xtype <- typeOfExpr vars types x
    case op of
      PrefixInc -> numberContext vars types xtype
      PrefixDec -> numberContext vars types xtype
      PrefixLNot -> boolContext vars types xtype
      PrefixBNot -> numberContext vars types xtype
      PrefixPlus -> numberContext vars types xtype
      PrefixMinus -> numberContext vars types xtype
      PrefixTypeof -> return $ types ! "string"
      PrefixDelete -> return $ types ! "bool" --TODO: remove delete?

  InfixExpr a op l r -> do
    ltype <- typeOfExpr vars types l
    rtype <- typeOfExpr vars types r
    let numstobool = do --more efficient if this function is lifted and takes args?
          numberContext vars types ltype
          numberContext vars types rtype
          return $ types ! "bool"
    case op of
      OpLT -> numstobool
      OpLEq -> numstobool
      OpGT -> numstobool
      OpGEq -> numstobool
      OpIn -> fail "NYI"
      OpInstanceof -> fail "NYI"
      OpEq -> fail "NYI"
      OpNEq -> fail "NYI"
      OpStrictEq -> return $ types ! "bool"
      OpStrictNEq -> return $ types ! "bool"

      --OpLAnd -> 
  {- OpLAnd | OpLOr 
             | OpMul | OpDiv | OpMod  | OpSub | OpLShift | OpSpRShift
             | OpZfRShift | OpBAnd | OpBXor | OpBOr | OpAdd -}
             
  --TODO: what about monads let's you do let x = 5 without an "in" ?
  CondExpr a c t e -> do
    ctype <- typeOfExpr vars types c 
    boolContext vars types ctype --boolContext will fail if something goes wrong
    ttype <- typeOfExpr vars types t
    etype <- typeOfExpr vars types e
    if (ttype /= etype) 
      then fail $ "then and else must have the same type in a ternary expression"
      else return ttype
    
  AssignExpr a op lhs rhs -> fail "NYI"

  ParenExpr a x -> typeOfExpr vars types x
  ListExpr a exprs -> do
    typelist <- mapM (typeOfExpr vars types) exprs
    return $ last typelist
  
  CallExpr a funcexpr argexprs -> fail "NYI"
  FuncExpr a argnames functype bodystmt -> do
    functype <- resolveType vars types functype
    case functype of
      TFunc a thistype reqargs optargs vararg rettype -> fail "NYI"
      _ -> fail "Function must have a function type."

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

typeCheckStmt :: (Monad m) => Env -> Env -> (Statement SourcePos) -> m Bool
typeCheckStmt vars types stmt = case stmt of 
  BlockStmt pos stmts -> do
    results <- mapM (typeCheckStmt vars types) stmts
    return $ all id results
  EmptyStmt pos -> return True
  ExprStmt  pos expr -> do
    typeOfExpr vars types expr
    return True
  IfStmt pos c t e -> do
     ctype <- typeOfExpr vars types c
     case ctype of
       TId _ "bool" -> do
         results <- mapM (typeCheckStmt vars types) [t, e]
         return $ all id results
       _ -> fail "test expression must be a boolean"
  IfSingleStmt pos c t -> do
     ctype <- typeOfExpr vars types c
     case ctype of
       TId _ "bool" -> (typeCheckStmt vars types t)
       _ -> fail "test expression must be a boolean"
  SwitchStmt pos expr clauses -> do
     typeOfExpr vars types expr 
     results <- mapM (\c -> do case c of 
                                CaseClause pos expr stmts -> do
                                  typeOfExpr vars types expr
                                  results <- mapM (typeCheckStmt vars types) stmts
                                  return $ all id results
                                CaseDefault pos stmts -> do
                                  results <- mapM (typeCheckStmt vars types) stmts
                                  return $ all id results)
                clauses
     return $ all id results
  WhileStmt pos expr statement -> do
     typeOfExpr vars types expr
     typeCheckStmt vars types statement
  DoWhileStmt pos statement expr -> do
     res <- typeCheckStmt vars types statement
     typeOfExpr vars types expr
     return res
  BreakStmt _ _ -> return True
  ContinueStmt _ _ -> return True
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

typeCheckStmts :: (Monad m) => Env -> Env -> [(Statement SourcePos)] -> m Bool
typeCheckStmts vars types stmts = typeCheckStmt vars types $ BlockStmt (initialPos "[]") stmts




