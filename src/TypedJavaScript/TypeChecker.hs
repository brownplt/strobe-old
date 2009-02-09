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
   | otherwise               = fail $ "expected int or double, got " ++ (show t)

boolContext :: (Monad m) => Env -> Env -> (Type SourcePos) -> m (Type SourcePos)
boolContext vars types t
    | t == (types ! "bool") = return t
    | otherwise             = fail $ "expected bool, got " ++ show t

-- is t1 a subtype of t2? so far, just plain equality.
isSubType :: Env -> Env -> (Type SourcePos) -> (Type SourcePos) -> Bool
isSubType vars types t1 t2 = (t1 == t2)
{-
isRetSubType :: (Monad m) => Env -> Env -> (Type SourcePos) -> (Statement SourcePos) -> m Bool
isRetSubType vars types rettype (ReturnStmt _ mret) = if rettype == (types ! "undefined")
  then maybe (return True) (\_ -> (return False)) mret
  else case mret of
         Nothing -> False
         Just mretexpr -> do 
           mrettype <- typeOfExpr vars types mretexpr
           return $ isSubType vars types mrettype rettype-}
           
-- recursively resolve the type down to TApp, or a TFunc and a TObject containing
-- only resolved types
-- TODO: is it fine that this ISNT a Monad?
resolveType :: Env -> Env -> (Type SourcePos) -> (Type SourcePos)
resolveType vars types t = case t of
  TId _ s -> types ! s
  TFunc pos this reqargs optargs vararg rettype -> do
    let rt = (resolveType vars types)
        rtm = maybe Nothing (Just . rt)
    TFunc pos (rtm this) (map rt reqargs) (map rt optargs) (rtm vararg) (rt rettype)
  _ -> t

-- returns whether or not all possible paths return, and whether those return statements return subtypes of
-- the supplied type
-- motivation: when checking functions with return values, at least one of the statements must have all
-- paths returning.
allPathsReturn :: (Monad m) => Env -> Env -> (Type SourcePos) -> (Statement SourcePos) -> m Bool
allPathsReturn vars types rettype stmt = case stmt of
  BlockStmt _ stmts -> do
    results <- mapM (allPathsReturn vars types rettype) stmts
    return $ any id results
  IfStmt _ _ t e -> do
    results <- mapM (allPathsReturn vars types rettype) [t, e]
    return $ any id results
  IfSingleStmt _ _ t -> return False
  SwitchStmt _ _ clauses -> do
    -- TODO: True if there is a default clause where all paths return, False otherwise
    fail "allPathsReturn, SwitchStmt, NYI" 
  WhileStmt _ _ body -> allPathsReturn vars types rettype body
  DoWhileStmt _ body _ -> allPathsReturn vars types rettype body
  ForInStmt _ _ _ body -> allPathsReturn vars types rettype body
  ForStmt _ _ _ _ body -> allPathsReturn vars types rettype body
  TryStmt _ body catches mfinally -> fail "allPathsReturn, TryStmt, NYI" -- true if all catches and the finally have a return
  ThrowStmt{} -> return True
  ReturnStmt _ (Just expr) -> if (rettype == (types ! "undefined"))
    --TODO: decide what to do about functions with undefined return type - should they
    --      be allowed to return anything? should they be required to have empty return stmts?
    --      should they be allowed to have return statements, but only if their type is undefined?
    then fail "Cannot return anything from a functino whose return type is undefined"
    else do
      exprtype <- typeOfExpr vars types expr
      if isSubType vars types exprtype rettype
        then return True
        else fail $ (show exprtype) ++ " is not a subtype of the expected return type, " ++ (show rettype)
  
  ReturnStmt _ Nothing -> if (rettype == (types ! "undefined"))
    then return True
    else fail "found empty return in a function whose return type is not undefined"
  
  -- any other statement does not return from the function
  _ -> return False

-- given the current var and type environment, and a raw environment representing
-- new variable declarations from, for example, a function, return the new var
-- environment or fail on type error.
-- the variables initialized with expressions can reference other variables in the rawenv, but only
-- those declared above them.
processRawEnv :: (Monad m) => Env -> Env -> RawEnv -> m Env
processRawEnv vars types [] = return vars
processRawEnv vars types ((Id _ varname, Left expr):rest) = do
  exprtype <- typeOfExpr vars types expr
  processRawEnv (M.insert varname exprtype vars) types rest
processRawEnv vars types ((Id _ varname, Right vartype):rest) =
  processRawEnv (M.insert varname (resolveType vars types vartype) vars) types rest

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

  ArrayLit a exprs   -> fail "arrays NYI"
  ObjectLit a props  -> fail "objects NYI"

  ThisRef a          -> return $ vars ! "this"
  VarRef a (Id _ s)  -> maybe (fail ("unbound ID: " ++ s)) return (M.lookup s vars)

  DotRef a expr id   -> fail "dotref NYI"
  BracketRef a xc xk -> fail "bracketref NYI"
  NewExpr a xcon xvars -> fail "newexpr NYI"
  
{- 
data AssignOp = OpAssign | OpAssignAdd | OpAssignSub | OpAssignMul | OpAssignDiv
  | OpAssignMod | OpAssignLShift | OpAssignSpRShift | OpAssignZfRShift
  | OpAssignBAnd | OpAssignBXor | OpAssignBOr
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
      
      OpIn -> case rtype of 
                TObject{} -> return $ types ! "bool"
                _         -> fail $ "rhs of 'in' must be an object, got " ++  show rtype
      
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
    
  AssignExpr a op lhs rhs -> fail "assigning NYI"

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

  FuncExpr _ argnames functype' bodyblock@(BlockStmt _ bodystmts) -> do
    let functype = resolveType vars types functype'
    case functype of
      TFunc _ _ [argtype] _ _ rettype -> do
        if length argnames /= 1 
          then fail $ "Inconsistent function definition - argument number mismatch in arglist and type"
          else do let (Id _ arg0) = argnames !! 0
                      vars' = (M.insert arg0 argtype vars)
                  vars' <- processRawEnv vars' types (globalEnv bodystmts)
                  guaranteedReturn <- allPathsReturn vars' types rettype bodyblock 
                  if rettype /= (types ! "undefined") && (not guaranteedReturn)
                    then fail "Some path doesn't return a value, but the function's return type is not undefined"
                    else do
                      typeCheckStmt vars' types bodyblock
                      return functype
          
      TFunc _ _ _ _ _ _ -> fail "Only functions with one required argument are implemented."

      _ -> fail $ "Function must have a function type, given " ++ show functype

  FuncExpr _ _ _ _ -> fail "Function's body must be a BlockStmt" --just in case the parser fails somehow.

-- type check everything except return statements, handled in typeOfExpr _ _ FuncExpr{},
-- and var declarations, handled in whatever calls typeCheckStmt; both cases use
-- Environment.hs .
-- return True, or fail
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
     boolContext vars types ctype
     results <- mapM (typeCheckStmt vars types) [t, e]
     return $ all id results
  IfSingleStmt pos c t -> do
     ctype <- typeOfExpr vars types c
     boolContext vars types ctype
     result <- typeCheckStmt vars types t
     return result

  {-SwitchStmt pos expr clauses -> do
     typeOfExpr vars types expr 
     -- TODO: ensure only one default clause
     results <- mapM (\c -> do case c of 
                                CaseClause pos expr stmts -> do
                                  typeOfExpr vars types expr
                                  results <- mapM (typeCheckStmt vars types) stmts
                                  return $ all id results
                                CaseDefault pos stmts -> do
                                  results <- mapM (typeCheckStmt vars types) stmts
                                  return $ all id results)
                clauses
     return $ all id results-}
     
  WhileStmt pos expr statement -> do
     exprtype <- typeOfExpr vars types expr
     boolContext vars types exprtype     
     typeCheckStmt vars types statement
  DoWhileStmt pos statement expr -> do
     res <- typeCheckStmt vars types statement
     exprtype <- typeOfExpr vars types expr
     boolContext vars types exprtype
     return res
   
  BreakStmt _ _ -> return True
  ContinueStmt _ _ -> return True
  LabelledStmt _ _ stmt -> typeCheckStmt vars types stmt
  
  ForInStmt _ (ForInVar (Id _ varname) vartype) inexpr body -> 
    fail "for..in loops NYI"
  ForInStmt _ (ForInNoVar (Id _ varname)) inexpr body -> 
    fail "for..in loops NYI"
    
  ReturnStmt{} -> return True --handled elsewhere  
  VarDeclStmt{} -> return True -- handled elsewhere
  

{-
data Statement a
  = SwitchStmt a (Expression a) [CaseClause a]
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




