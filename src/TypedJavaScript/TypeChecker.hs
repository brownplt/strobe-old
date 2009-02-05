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
type Env = Map String (Type SourcePos)

resolveType :: (Monad m) => Env -> Env -> (Type SourcePos) -> m (Type SourcePos)
resolveType vars types t = case t of
  TId _ s -> return $ types ! s
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
-- for now, we're making this a lot stricter:
numberContext :: (Monad m) => Env -> Env -> (Type SourcePos) -> m (Type SourcePos)
numberContext vars types t
   | t == (types ! "int")    = return t
   | t == (types ! "double") = return t
   | otherwise               = fail $ "expected int or double, got " ++ (show t) ++ ", (types!'double')==" ++ show (types ! "double")

boolContext :: (Monad m) => Env -> Env -> (Type SourcePos) -> m (Type SourcePos)
boolContext vars types t
    | t == (types ! "bool") = return t
    | otherwise             = fail $ "expected bool, got " ++ show t

-- is t1 a subtype of t2? so far, just plain equality.
isSubType :: Env -> Env -> (Type SourcePos) -> (Type SourcePos) -> Bool
isSubType vars types t1 t2 = (t1 == t2)

-- we need two environments - one mapping variable id's to their types, and
-- one matching type id's to their type. types gets extended with external and type statements.
-- this function reduces everything to TObject, TFunc, or a base-case TApp.
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

  ThisRef a          -> return $ vars ! "this"
  VarRef a (Id _ s)  -> return $ vars ! s

  DotRef a expr id   -> fail "NYI"
  BracketRef a xc xk -> fail "NYI"
  NewExpr a xcon xvars -> fail "NYI"
  
{- 
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
      PrefixBNot -> do ntype <- numberContext vars types xtype
                       if ntype == types ! "int"
                         then return $ types ! "int"
                         else fail $ "~ operates on integers, got " ++ show xtype ++ " converted to " ++ show ntype
      PrefixPlus -> numberContext vars types xtype
      PrefixMinus -> numberContext vars types xtype
      PrefixTypeof -> return $ types ! "string"
      PrefixDelete -> return $ types ! "bool" --TODO: remove delete?

  InfixExpr a op l r -> do
    -- TODO: is the monadism bad because it kills chances for automatic parallelization of our code? =(.
    ltype <- typeOfExpr vars types l
    rtype <- typeOfExpr vars types r
    let relation = 
          if (ltype == (types ! "string") && rtype == (types ! "string"))
            then return $ types ! "bool"
            else do
              numberContext vars types ltype
              numberContext vars types rtype
              return $ types ! "bool"
        logical = do
          boolContext vars types ltype
          boolContext vars types rtype
          return $ types ! "bool"
        numop = \requireInts alwaysDouble -> do
          ln <- numberContext vars types ltype
          rn <- numberContext vars types rtype
          if (ln == types ! "int" && rn == types ! "int") -- all integers
            then if alwaysDouble 
              then return $ types ! "double" --e.g. division
              else return $ types ! "int" --e.g. +, -, *
            else if requireInts
              then fail $ "lhs and rhs must be ints, got " ++ show ln ++ ", " ++ show rn
              else return $ types ! "double"
              
    case op of
      OpLT  -> relation
      OpLEq -> relation
      OpGT  -> relation
      OpGEq -> relation
      
      OpIn | rtype == (types ! "object") -> return $ types ! "bool"
           | otherwise -> fail $ "rhs of 'in' must be an object, got " ++  show rtype
      
      OpInstanceof -> case rtype of
        TFunc _ _ _ _ _ _ -> return $ types ! "bool"
        _                 -> fail $ "rhs of 'instanceof' must be constructor, got " ++  show rtype

      --TODO: i forgot what we said about equality. assume they all work for now:
      OpEq  -> return $ types ! "bool" 
      OpNEq -> return $ types ! "bool"      
      OpStrictEq  -> return $ types ! "bool"
      OpStrictNEq -> return $ types ! "bool"
      
      OpLAnd -> logical 
      OpLOr  -> logical

      OpMul  -> numop False False
      OpDiv  -> numop False True
      OpMod  -> numop False False
      OpSub  -> numop False True
      OpLShift   -> numop True False
      OpSpRShift -> numop True False
      OpZfRShift -> numop True False
      OpBAnd -> numop True False
      OpBXor -> numop True False
      OpBOr  -> numop True False
      OpAdd  -> do
        -- from TDGTJ: 
        -- If one operand is a string, the other is converted, and they are concatenated.
        -- objects are converted to numbers or strings and then added or concatenated
        -- first valueOf is tried - if numbers result, then numbers are added
        -- then toString is tried. if toString returns a number, numbers are added.
        -- if it returns a string, then strings are concatenated.
        -- for now, let's just do strings or numbers:
        if ltype == (types ! "string") || rtype == (types ! "string") 
          then return $ types ! "string"
          else numop False False
      
  CondExpr a c t e -> do
    ctype <- typeOfExpr vars types c 
    boolContext vars types ctype --boolContext will fail if something goes wrong with 'c'
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
  
  CallExpr a funcexpr argexprs -> do
    functype <- typeOfExpr vars types funcexpr
    case functype of 
      TFunc _ _ [funcargtype] _ _ funcrettype -> do
        if length argexprs /= 1
          then fail $ "Only functions with one required argument are implemented."
          else do
            argexprtype <- typeOfExpr vars types $ argexprs !! 0
            if isSubType vars types argexprtype funcargtype
              then return funcrettype
              else fail $ (show argexprtype) ++ " is not a subtype of the expected argument type, " ++ show funcargtype
      _ -> fail $ "Expected function with 1 arg, got " ++ show functype

  FuncExpr a argnames functype bodystmt -> do
    functype <- resolveType vars types functype
    case functype of
      TFunc _ _ [argtype] _ _ rettype -> do
        if length argnames /= 1 
          then fail $ "Inconsistent function definition - argument number mismatch in arglist and type"
          else case bodystmt of
            BlockStmt _ [ReturnStmt _ (Just expr)] -> do
              let (Id _ arg0) = argnames !! 0
              exprtype <- typeOfExpr (M.insert arg0 argtype vars) types expr
              if isSubType vars types exprtype rettype
                then return functype
                else fail $ (show exprtype) ++ " is not a subtype of the expected return type, " ++ show rettype

            BlockStmt _ [ReturnStmt _ Nothing] -> do
              if rettype /= (types ! "undefined")
                then fail $ "Function must return a " ++ (show rettype) ++ ", not nothing" 
                else return $ types ! "undefined"

            _ -> fail "Only functions with a single return statement are implemented"

      TFunc _ _ _ _ _ _ -> fail "Only functions with one required argument are implemented."

      _ -> fail $ "Function must have a function type, given " ++ show functype


typeCheckStmt :: (Monad m) => Env -> Env -> (Statement SourcePos) -> m Bool
typeCheckStmt vars types stmt = case stmt of 
  BlockStmt pos stmts -> do
    results <- mapM (typeCheckStmt vars types) stmts
    return $ all id results
  EmptyStmt pos -> return True
  ExprStmt  pos expr -> do
    typeOfExpr vars types expr
    return True
  {-IfStmt pos c t e -> do
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
       _ -> fail "test expression must be a boolean"-}
  SwitchStmt pos expr clauses -> do
     typeOfExpr vars types expr 
     -- TODO: ensure only one default clause?
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
  WhileStmt pos expr statement -> do --TODO: add bool context checking here
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




