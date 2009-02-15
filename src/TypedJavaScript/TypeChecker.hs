module TypedJavaScript.TypeChecker
  ( typeOfExpr
  , resolveType
  , typeCheckStmt
 -- , typeCheckStmts
  , isSubType
  , Env
  , corePos
  , coreTypeEnv
  , coreVarEnv
  ) where

import Data.Generics
import Data.List (foldl', nub)
import qualified Data.Map as M
import Data.Map(Map, (!))
import Control.Monad(liftM, zipWithM)

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
coreVarEnv = M.fromList [("this", coreTypeEnv ! "@global"),
                         ("undefined", coreTypeEnv ! "undefined")]

-- TODO: deal with TApp, add syntax for defining them , etc.

-- in pJS, anything can be used in a number and bool context without anything crashing.
-- for now, we're making this a lot stricter:
numberContext :: (Monad m) => Env -> Env -> (Type SourcePos) -> m (Type SourcePos)
numberContext vars types t
   | t == (types ! "int")    = return t
   | t == (types ! "double") = return t
   | otherwise               = fail $ "expected int or double, got " ++ (show t)

-- bool is also much freer in pJS. 
boolContext :: (Monad m) => Env -> Env -> (Type SourcePos) -> m (Type SourcePos)
boolContext vars types t
    | t == (types ! "bool") = return t
    | otherwise             = fail $ "expected bool, got " ++ show t

-- is t1 a subtype of t2? so far, just plain equality.
isSubType :: Env -> Env -> (Type SourcePos) -> (Type SourcePos) -> Bool
isSubType vars types (TObject _ props1) (TObject _ props2) =
  all (\(o2id@(Id _ o2propname), o2proptype) ->
         (case lookup o2id props1 of 
            Nothing -> False --o1 must have everything o2 does
            Just o1proptype -> isSubType vars types o1proptype o2proptype))
      props2

isSubType vars types t1 t2 
 | (t1 == t2) = True
 | (t1 == types ! "undefined") = True --everything is nullable
 | (t1 == types ! "int") = t2 == types ! "double"
 | otherwise = False

{-
isRetSubType :: (Monad m) => Env -> Env -> (Type SourcePos) -> (Statement SourcePos) -> m Bool
isRetSubType vars types rettype (ReturnStmt _ mret) = if rettype == (types ! "undefined")
  then maybe (return True) (\_ -> (return False)) mret
  else case mret of
         Nothing -> False
         Just mretexpr -> do 
           mrettype <- typeOfExpr vars types mretexpr
           return $ isSubType vars types mrettype rettype-}
           
-- recursively resolve the type down to TApp, or a TFunc or a TObject containing
-- only resolved types
resolveType :: Env -> Env -> (Type SourcePos) -> (Type SourcePos)
resolveType vars types t = case t of
  TId _ s -> types ! s
  TFunc pos this reqargs optargs vararg rettype -> do
    let rt = (resolveType vars types)
        rtm = maybe Nothing (Just . rt) --i am proud of this line
    TFunc pos (rtm this) (map rt reqargs) (map rt optargs) (rtm vararg) (rt rettype)
  TObject pos props -> if (map fst props) /= nub (map fst props)
    then error "duplicate property name in object type."
    else TObject pos $ map (\(id,t) -> (id, resolveType vars types t)) props
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
  TryStmt _ body catches mfinally -> fail "allPathsReturn, TryStmt, NYI" -- true if all catches and/or the finally have a return
  ThrowStmt{} -> return True
  ReturnStmt _ (Just expr) -> if (rettype == (types ! "undefined"))
    --TODO: decide what to do about functions with undefined return type - should they
    --      be allowed to return anything? should they be required to have empty return stmts?
    --      should they be allowed to have return statements, but only if their type is undefined?
    --      all of these should be fine, since anything using the function's return value would be
    --      unable to do anything with it.
    then fail "cannot return anything from a function whose return type is undefined"
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
-- new variable declarations from, for example, a function, return the new variables
-- environment or fail on type error.
-- the variables initialized with expressions can reference other variables in the rawenv, but only
-- those declared above them.
-- the third argument is a list of IDs that this rawenv is forbidden to override
-- this starts off with just the function arguments, and each added variable is added to the list
processRawEnv :: (Monad m) => Env -> Env -> [String] -> RawEnv -> m Env
processRawEnv vars types _ [] = return vars
processRawEnv vars types _ ((Id _ varname, Nothing, Nothing):rest) = 
  fail "Invalid RawEnv contains var that has neither type nor expression"
processRawEnv vars types forbidden (entry@(Id _ varname,_,_):rest) = 
  if elem varname forbidden
    then fail $ "Can't re-define " ++ varname
    else case entry of
      (Id _ varname, Nothing, Just expr) -> do
        exprtype <- typeOfExpr vars types expr
        processRawEnv (M.insert varname exprtype vars) types (varname:forbidden) rest
      (Id _ varname, Just vartype, Nothing) -> do
        let vartype' = (resolveType vars types vartype)
        --seq because we want an error instantly, even if the variable is declared but never used
        --TODO: change resolveType to a Monad, since it can fail now?
        seq vartype' $ processRawEnv (M.insert varname vartype' vars) 
                         types (varname:forbidden) rest
      (Id _ varname, Just vartype, Just expr) -> do
        exprtype <- typeOfExpr vars types expr
        let vartype' = (resolveType vars types vartype)
        seq vartype' $ 
          if not $ isSubType vars types exprtype vartype'
            then fail $ "expression " ++ (show expr) ++ 
                        " has type " ++ (show exprtype) ++ 
                        " which is not a subtype of declared type " ++ (show vartype')
            else processRawEnv (M.insert varname vartype' vars) types (varname:forbidden) rest

-- we need two environments - one mapping variable id's to their types, and
-- one matching type id's to their type. types gets extended with type statements,
-- variables with vardecls and 'external' statements.
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
  ObjectLit pos props  -> let
      procProps [] = return []
      --TODO: object literals technically _could_ have numbers in them, they just
      --TODO: wouldn't be accessible with our syntax. should we fail if we see them?
      procProps ((prop, giventype, expr):rest) = do
        --TODO: this might be refactorable into processRawEnv
        exprtype <- typeOfExpr vars types expr
        let giventype' = maybe exprtype (resolveType vars types) giventype
        if not $ isSubType vars types exprtype giventype' 
          then fail $ "expression " ++ (show expr) ++ 
                      " has type " ++ (show exprtype) ++ 
                      " which is not a subtype of declared type " ++ (show giventype')
          else do
            let thisprop = (Id pos (propToString prop), giventype')
            restprops <- procProps rest
            if elem (propToString prop) $ map (\((Id _ s),_) -> s) restprops
              then fail $ "duplicate property name in object literal: " ++ (propToString prop)
              else return (thisprop:restprops)
   in liftM (TObject pos) (procProps props)

  ThisRef a          -> return $ vars ! "this"
  VarRef a (Id _ s)  -> maybe (fail ("unbound ID: " ++ s)) return (M.lookup s vars)

  DotRef a expr id     -> fail "dotref NYI"
  BracketRef a xc xk   -> fail "bracketref NYI"
  NewExpr a xcon xvars -> fail "newexpr NYI"
  
  PostfixExpr a op x -> do
    xtype <- typeOfExpr vars types x
    numberContext vars types xtype
  
  PrefixExpr a op x -> do
    xtype <- typeOfExpr vars types x
    case op of
      PrefixInc    -> numberContext vars types xtype
      PrefixDec    -> numberContext vars types xtype
      PrefixLNot   -> boolContext vars types xtype
      PrefixBNot   -> do ntype <- numberContext vars types xtype
                         if ntype == types ! "int"
                           then return $ types ! "int"
                           else fail $ "~ operates on integers, got " ++ show xtype ++ 
                                       " converted to " ++ show ntype
      PrefixPlus   -> numberContext vars types xtype
      PrefixMinus  -> numberContext vars types xtype
      PrefixTypeof -> return $ types ! "string"
      PrefixDelete -> return $ types ! "bool" --TODO: remove delete? add checks for readonly fields, etc.

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

      -- true == "1" will evaluate to true in tJS...
      OpEq        -> return $ types ! "bool" 
      OpNEq       -> return $ types ! "bool"      
      OpStrictEq  -> return $ types ! "bool"
      OpStrictNEq -> return $ types ! "bool"
      
      OpLAnd -> logical 
      OpLOr  -> logical

      OpMul      -> numop False False
      OpDiv      -> numop False True
      OpMod      -> numop False True
      OpSub      -> numop False False
      OpLShift   -> numop True False
      OpSpRShift -> numop True False
      OpZfRShift -> numop True False
      OpBAnd     -> numop True False
      OpBXor     -> numop True False
      OpBOr      -> numop True False
      OpAdd      -> do
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
      
  AssignExpr a op lhs rhs -> 
    -- TDGTJ: "In JavaScript, variables, properties of objects, and elements of arrays are lvalues." p62.
    let rewrite infixop = typeOfExpr vars types (AssignExpr a OpAssign lhs (InfixExpr a infixop lhs rhs))
        procasgn = do
          ltype <- typeOfExpr vars types lhs
          rtype <- typeOfExpr vars types rhs
          case op of
            OpAssign -> if isSubType vars types rtype ltype 
              then return ltype
              else fail $ "in assignment, rhs " ++ (show rtype) ++ " is not a subtype of lhs " ++ (show ltype)
            OpAssignAdd -> rewrite OpAdd
            OpAssignSub -> rewrite OpSub
            OpAssignMul -> rewrite OpMul
            OpAssignDiv -> rewrite OpDiv
            OpAssignMod -> rewrite OpMod
            OpAssignLShift -> rewrite OpLShift
            OpAssignSpRShift -> rewrite OpSpRShift
            OpAssignZfRShift -> rewrite OpZfRShift
            OpAssignBAnd -> rewrite OpBAnd
            OpAssignBXor -> rewrite OpBXor
            OpAssignBOr -> rewrite OpBOr
     in case lhs of
          VarRef{} -> procasgn
          DotRef{} -> procasgn
          BracketRef{} -> procasgn
          _ -> fail "lhs of assignment must be an lvalue: a variable, an object property, or an array element"
  
  CondExpr a c t e -> do
    ctype <- typeOfExpr vars types c 
    boolContext vars types ctype --boolContext will fail if something goes wrong with 'c'
    ttype <- typeOfExpr vars types t
    etype <- typeOfExpr vars types e
    -- TODO: potentially find the most common supertype of ttype and etype, and evaluate to that
    -- so, returning 3 and 4.0 would give you a double.
    -- {x: 5, y: 6} and {x: 5} would give you an {x: int}.
    if (ttype /= etype) 
      then fail $ "then and else must have the same type in a ternary expression"
      else return ttype
    
  ParenExpr a x -> typeOfExpr vars types x
  ListExpr a exprs -> do
    typelist <- mapM (typeOfExpr vars types) exprs
    return $ last typelist

  CallExpr a funcexpr argexprs -> do
    functype <- typeOfExpr vars types funcexpr
    case functype of 
      TFunc _ Nothing reqargtypes optargtypes Nothing rettype -> do
        let s = length argexprs
        let r = length reqargtypes
        let z = length optargtypes
        if r > s || s > (r + z)
          then if r > s
                 then fail $ "expected at least" ++ (show r) ++ " arguments, got only " ++ (show s)
                 else fail $ "expected at most" ++ (show (r+z)) ++ " args, but got " ++ (show s)
          else do
            zipWithM (\argexpr expectedtype -> 
              do
                argexprtype <- typeOfExpr vars types argexpr
                if isSubType vars types argexprtype expectedtype
                  then return True
                  else fail $ (show argexprtype) ++ " is not a subtype of the expected argument type, " 
                              ++ show expectedtype)
              argexprs (reqargtypes ++ optargtypes)
            return rettype
      _ -> fail $ "Expected function with only reqargs, got " ++ show functype

  FuncExpr _ argnames functype' bodyblock@(BlockStmt _ bodystmts) -> do
    let functype = resolveType vars types functype'
    case functype of
      TFunc _ Nothing reqargtypes optargtypes Nothing rettype -> do
        if length argnames /= (length reqargtypes) + (length optargtypes)
          then fail $ "Inconsistent function definition - argument number mismatch in arglist and type"
          else do
            vars' <- processRawEnv vars types [] 
                                   ((zipWith (\a b -> (a, Just b, Nothing)) argnames (reqargtypes++optargtypes)) ++ 
                                    (globalEnv bodystmts))
            guaranteedReturn <- allPathsReturn vars' types rettype bodyblock 
            if rettype /= (types ! "undefined") && (not guaranteedReturn)
              then fail "Some path doesn't return a value, but the function's return type is not undefined"
              else do
                typeCheckStmt vars' types bodyblock
                return functype
                      
      TFunc _ _ _ _ _ _ -> fail "Only functions with required and opt args are implemented."

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
    
  ForStmt _ init test incr body -> do
    --var decls in the init are already processed by now
    let checkinit = case init of
          ExprInit expr -> (typeOfExpr vars types expr >> return True)
          _ -> return True
--        parsetest = case test of
          
    checkinit
    testtype <- maybe (return $ types ! "bool") (typeOfExpr vars types) test
    boolContext vars types testtype
    --we don't care about the incr type, but it has to type-check
    --we use (types ! "bool") as filler so that 'maybe' can type properly
    maybe (return $ types ! "bool") (typeOfExpr vars types) incr
    typeCheckStmt vars types body
    
  ReturnStmt{} -> return True --handled elsewhere  
  VarDeclStmt{} -> return True -- handled elsewhere
  

{- Statements left over:

data Statement a
  = SwitchStmt a (Expression a) [CaseClause a]
  | ForInStmt a (ForInInit a) (Expression a) (Statement a)
  | TryStmt a (Statement a) {-body-} [CatchClause a] {-catches-}
      (Maybe (Statement a)) {-finally-}
  | ThrowStmt a (Expression a)
  -- TODO: add generics to functions/constructors?
  -- | FunctionStmt a (Id a) {-name-} [(Id a, Type a)] {-args-} (Maybe (Type a)) {-ret type-}  (Statement a) {-body-}
  | ConstructorStmt a (Id a) {-name-} 
                      [(Id a, Type a)] {- required args -}
                      [(Id a, Type a)] {- optional args -}
                      (Maybe (Id a, Type a)) {- optional var arg -}
                      (Statement a) {-body-}
  | TypeStmt a (Id a) (Type a) -- e.g. type Point :: {x :: int, y :: int};
  
  -}

--typeCheckStmts :: (Monad m) => Env -> Env -> [(Statement SourcePos)] -> m Bool
--typeCheckStmts vars types stmts = typeCheckStmt vars types $ BlockStmt (initialPos "[]") stmts




