module TypedJavaScript.TypeChecker
  ( typeOfExpr
  , typeCheckStmt
  , typeCheck
  , isSubType
  , Env
  , corePos
  , coreTypeEnv
  , coreVarEnv
  ) where

import Data.Generics
import qualified Data.Maybe as Y
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map(Map, (!))
import Control.Monad

import Text.ParserCombinators.Parsec(SourcePos)
import Text.ParserCombinators.Parsec.Pos
import TypedJavaScript.Syntax
import TypedJavaScript.Environment
import TypedJavaScript.Types

-- ----------------------------------------------------------------------------

-- |Type-checks a sequence of statemens. Returns the local environment.
typeCheck :: [Statement SourcePos] -- ^statements to type-check
          -> IO Env -- ^identifiers introduced by these statements
typeCheck stmts = do
  let rawEnv = globalEnv stmts
  env <- processRawEnv coreVarEnv coreTypeEnv [] rawEnv
  mapM_ (typeCheckStmt env coreTypeEnv) stmts
  return (M.difference env coreVarEnv)

corePos = initialPos "core"

-- TODO: figure out what to do with global.
globalObjectType = TObject corePos []

arrayFields :: [(String,Type SourcePos)]
arrayFields =
  [ ("length", TId corePos "int") 
  ]

coreTypeEnv :: Env
coreTypeEnv = M.fromList $ 
  (map (\s -> (s, (TId corePos s)))
       ["string", "double", "int", "any", "bool","Array"]) ++
  [("@global", globalObjectType), ("unit", unitType)]

coreVarEnv :: Env
coreVarEnv = M.fromList $ [("this", coreTypeEnv ! "@global")] ++
  --TODO: remove isInt et. al. as built-ins once they're no longer necessary
  [("isInt", makePred "int"),
   ("isDouble", makePred "double"),
   ("isString", makePred "string"),
   ("isBool", makePred "bool")]
 where
   makePred s = (TFunc corePos Nothing 
                    [coreTypeEnv ! "any"] Nothing
                    (coreTypeEnv ! "bool")
                    (LPType (coreTypeEnv ! s)))


-- TODO: deal with TApp, add syntax for defining them , etc.

-- in pJS, anything can be used in a number and bool context without 
-- anything crashing.for now, we're making this a lot stricter:
numberContext :: (Monad m) => Env -> Env -> (Type SourcePos) -> 
                              m (Type SourcePos)
numberContext vars types t
   | t == (types ! "int")    = return t
   | t == (types ! "double") = return t
   | otherwise               = fail $ "expected int or double, got " ++ (show t)

-- bool is also much freer in pJS. 
boolContext :: (Monad m) => Env -> Env -> (Type SourcePos) -> m (Type SourcePos)
boolContext vars types t
    | isSubType t (types ! "bool") = return t
    | otherwise = fail $ "expected sub-type of bool, got " ++ show t

(<:) :: Type SourcePos -> Type SourcePos -> Bool
x <: y = isSubType x y

isSubType :: Type SourcePos -> Type SourcePos -> Bool
--objects are invariant in their common field types
--TODO: verify that the 'case' here is well-founded, and that I'm not
--      doing something silly.
isSubType (TObject _ props1) (TObject _ props2) =
  all (\(o2id@(Id _ o2propname), o2proptype) -> maybe
        False (\o1proptype -> case (o1proptype,o2proptype) of
                  --want to preserve this subtype among object props:
                  (TObject{},TObject{}) -> isSubType 
                    o1proptype o2proptype
                  --but don't want subtype for other things:
                  _ -> o1proptype == o2proptype)     
              (lookup o2id props1))
      props2

isSubType f2@(TFunc _ this2 req2 var2 ret2 lp2)  -- is F2 <= F1?
          f1@(TFunc _ this1 req1 var1 ret1 lp1) =
  let ist = isSubType       
   in ist ret2 ret1                       --covariance of return types
      && length req2 >= length req1       --at least as many req args
      && (var2==Nothing || var1/=Nothing) --f2 has varargs -> f1 has varargs
      && (lp1 == lp2 || lp1 == LPNone) --from TypedScheme
      && --contravariance of arg types. TODO: fix this.
         (let maxargs = max (length req2 + (maybe 0 (const 1) var2)) 
                            (length req1 +  (maybe 0 (const 1) var1))
              all2    = (map Just $ req2 ++ (maybe [] repeat var2)) ++ repeat Nothing
              all1    = (map Just $ req1 ++ (maybe [] repeat var1)) ++ repeat Nothing
           in maybe False (all id) $ mapM id $ zipWith (liftM2 ist) (take maxargs all1) (take maxargs all2))

isSubType (TNullable _ t1) (TNullable _ t2) = t1 <: t2
isSubType t1 (TNullable _ t2) = t1 <: t2
--the first of these cases works if both are unions; the second does not.
{- 
(x U y) <: (x U y)
--------------------------
x <: x U y and y <: x U y
-----------------------------------------
(x <: x or x <: y) and (y <: x or y <: y)
-}
isSubType (TUnion _ ts) t = all (\ti -> ti <: t) ts
isSubType t (TUnion _ ts) = any (t <:) ts
isSubType _ (TId _ "any") = True -- TODO: O RLY?
isSubType (TId _ "int") (TId _ "double") = True
isSubType (TId _ x) (TId _ y) = x == y
isSubType (TApp _ (TId _ "Array") args1) (TApp _ (TId _ "Array") args2) =
  args1 == args2
isSubType (TApp _ c1 args1) (TApp _ c2 args2) = 
  c2 <: c1 &&
  (and $ zipWith (<:) args1 args2) &&
  (length args1 == length args2)
isSubType(TVal v1 t1) (TVal v2 t2) = v1 `eqLit` v2 && t1 <: t2
isSubType (TVal _ t1) t2 = t1 <: t2
isSubType (TForall ids1 t1) (TForall ids2 t2) = ids1 == ids2 && t1 == t2
isSubType _ _ = False

--get the most specific supertype. best = most specific to save typing.
--used for array literals and ternary expressions
--TODO: this no longer returns Nothing                            
bestSuperType :: Env -> Env -> (Type SourcePos) -> (Type SourcePos) -> 
                 Maybe (Type SourcePos)

-- best super type of two objects is an object that has as
-- many properties as are in both:
bestSuperType vars types (TObject pos1 props1) (TObject _ props2) = do
  --take everything that is in both objects. worst-case: {}.
  Just $ TObject (initialPos "bestSuperType") $ 
                 Y.mapMaybe (\(prop1id, t1) -> liftM ((,) prop1id) 
                              (lookup prop1id props2 >>= bestSuperType vars types t1)) 
                            props1 
--TODO: this no longer returns Nothing, so no need for it to return Maybe
bestSuperType vars types t1 t2
 | (t1 == t2) = Just t1
 | (isSubType t1 t2) = Just t2
 | (isSubType t2 t1) = Just t1
 | otherwise = Just $ flattenUnion vars types $ TUnion (typePos t1) [t1, t2] 


reduceUnion :: Type SourcePos -> Type SourcePos
reduceUnion (TUnion p ts) = TUnion p (map unTVal ts)
reduceUnion t = error $ "reduceUnion expected a TUnion, got " ++ show t

--take a union of many types and reduce it to the simplest one possible.
--Example: U(true, true, false, int, double, false) --> U(true, false, double)
--Example: U(U(true, int), false) --> U(true, false, int)
--So far, this just flattens the union
flattenUnion :: Env -> Env -> (Type SourcePos) -> (Type SourcePos)
flattenUnion vars types (TUnion pos ts) = 
  case (foldl
         (\res t -> case t of
                      TUnion _ tocomb -> res ++ tocomb
                      regular -> res ++ [regular])
         [] ts) of
   [onet] -> onet
   noneormanyt -> TUnion pos noneormanyt

flattenUnion vars types t = t

-- returns whether or not all possible paths return, and whether those
-- return statements return subtypes of the supplied type 
-- motivation: when checking functions with return values, at least
-- one of the statements must have all paths returning.
allPathsReturn :: (Monad m) => Env -> Env -> 
                  (Type SourcePos) -> (Statement SourcePos) -> m Bool
allPathsReturn vars types rettype stmt = case stmt of
  BlockStmt _ stmts -> do
    results <- mapM (allPathsReturn vars types rettype) stmts
    return $ any id results
  IfStmt _ _ t e -> do
    results <- mapM (allPathsReturn vars types rettype) [t, e]
    return $ any id results
  IfSingleStmt _ _ t -> return False
  SwitchStmt _ _ clauses -> do
    -- TODO: Switch: True if there is a default clause where all paths
    -- return, False otherwise
    fail "allPathsReturn, SwitchStmt, NYI" 
  WhileStmt _ _ body -> allPathsReturn vars types rettype body
  DoWhileStmt _ body _ -> allPathsReturn vars types rettype body
  ForInStmt _ _ _ body -> allPathsReturn vars types rettype body
  ForStmt _ _ _ _ body -> allPathsReturn vars types rettype body
  -- Try: true if all catches and/or the finally have a return
  TryStmt _ body catches mfinally -> fail "allPathsReturn, TryStmt, NYI" 
  ThrowStmt{} -> return True
  ReturnStmt _ (Just expr) -> do
    (exprtype, lp) <- typeOfExpr vars types expr
    if isSubType exprtype rettype
      then return True
      else fail $ (show exprtype) ++ " is not a subtype of the expected " ++
                  "return type, " ++ (show rettype)
  -- return; means we are returning unit.  If the return type is nullable,
  -- we have to return null;.
  ReturnStmt _ Nothing -> case isSubType unitType rettype of
    True -> return True
    False -> fail $ "expected return value of type " ++ show rettype
  -- any other statement does not return from the function
  _ -> return False

-- |If typeOfExpr returns a refined type (i.e. a 'TVal'), omit the refinement
-- and return the base type.
inferLocally :: (Monad m) => Env -> Env -> (Expression SourcePos) ->
                             m (Type SourcePos)
inferLocally vars types expr = do
  (exprtype, lp) <- typeOfExpr vars types expr
  case exprtype of
    (TVal _ t) -> return t
    otherwise -> return exprtype

-- given the current var and type environment, and a raw environment
-- representing new variable declarations from, for example, a
-- function, return the new variables environment or fail on type
-- error.  the variables initialized with expressions can reference
-- other variables in the rawenv, but only those declared above them.
-- the third argument is a list of IDs that this rawenv is forbidden
-- to override this starts off with just the function arguments, and
-- each added variable is added to the list
processRawEnv :: (Monad m) => Env -> Env -> [String] -> RawEnv -> m Env
processRawEnv vars types _ [] = return vars
processRawEnv vars types forbidden (entry@(Id _ varname,_,_):rest) = 
  if elem varname forbidden
    then fail $ "Can't re-define " ++ varname
    else case entry of
      (Id _ _, Nothing, Nothing) -> fail $ 
        "Invalid RawEnv contains var that has neither type nor expression"
      (Id _ varname, Nothing, Just expr) -> do
        --local type inference
        exprtype <- inferLocally vars types expr
        processRawEnv (M.insert varname exprtype vars) 
                      types (varname:forbidden) rest
      -- If a variable is declared with a type but is uninitialized,
      -- it must be TNullable (since it is initialized to undefined).
      (Id _ varname, Just vartype, Nothing) -> do
        let vartype' = vartype 
        case vartype' of
          TNullable _ _ -> processRawEnv (M.insert varname vartype' vars) types
                                         (varname:forbidden) rest
          otherwise -> fail $ "unintialized variables must have nullable " ++
                              "types (suffix '?')"
      (Id _ varname, Just vartype, Just expr) -> do
        (exprtype,lp) <- typeOfExpr vars types expr
        let vartype' = vartype 
        seq vartype' $ 
          if not $ isSubType exprtype vartype'
            then fail $ "expression " ++ (show expr) ++ 
                        " has type " ++ (show exprtype) ++ 
                        " which is not a subtype of declared type " ++ 
                        (show vartype')
            else processRawEnv (M.insert varname vartype' vars) 
                               types (varname:forbidden) rest

-- Helpers for occurrence typing, from TypedScheme paper
restrict :: Env -> Env ->
            (Type SourcePos) -> (Type SourcePos) -> (Type SourcePos)
restrict vars types s t
 | isSubType s t = s
 | otherwise = case t of
     TUnion pos ts -> flattenUnion vars types $ 
                        TUnion pos (map (restrict vars types s) ts)
     _ -> t

remove :: Env -> Env -> 
          (Type SourcePos) -> (Type SourcePos) -> (Type SourcePos)
remove vars types s t
 | isSubType s t = TUnion (typePos s) []
 | otherwise = case t of
     TUnion pos ts -> flattenUnion vars types $ 
                        TUnion pos (map (remove vars types s) ts)
     --TODO: make sure remove is correct
     _ -> flattenUnion vars types $ 
            TUnion (typePos s) 
                   (filter (\hm -> not $ isSubType hm t)
                           (case s of
                             TUnion _ ts -> ts
                             _ -> [s]))
     
--TODO: in TS, 'false' is false, and everything else is true the same
--is not true in JS, so we have to think about how to handle gammaPlus
--and gammaMinus with VPIds.

gammaPlus :: Env -> Env -> (VisiblePred SourcePos) -> Env
gammaPlus vars types (VPType t x) = 
  M.insert x (restrict vars types (vars ! x) t) vars
--gammaPlus vars types (VPId x) = M.insert x (remove (G ! x), falseType)
gammaPlus vars types (VPId x) = error "Gamma + VPId NYI" 
gammaPlus vars types _ = vars

gammaMinus :: Env -> Env -> VisiblePred SourcePos -> Env
gammaMinus vars types (VPType t x) = 
  M.insert x (remove vars types (vars ! x) t) vars
--gammaMinus vars types (VPId x) = M.insert x falseType
gammaMinus vars types (VPId x) = error "Gamma - VPId NYI" 
gammaMinus vars types _ = vars

combpred :: VisiblePred SourcePos -> VisiblePred SourcePos -> 
            VisiblePred SourcePos -> VisiblePred SourcePos
combpred (VPType t x1) VPTrue (VPType s x2) =
  if (x1 == x2) 
    then VPType (TUnion (typePos t) [t, s]) x1 --flattenUnion here?
    else VPNone
combpred VPTrue f1 f2 = f1
combpred VPFalse f1 f2 = f2
combpred f VPTrue VPFalse = f
combpred f1 f2 f3 = if f2 == f3 then f2 else VPNone

-- we need two environments - one mapping variable id's to their
-- types, and one matching type id's to their type. types gets
-- extended with type statements, variables with vardecls and
-- 'external' statements.  this function reduces everything to
-- TObject, TFunc, or a base-case TApp.
-- This function returns the type, as well as the visible predicate
typeOfExpr :: (Monad m) => Env -> Env -> (Expression SourcePos) -> 
                           m (Type SourcePos, VisiblePred SourcePos)
typeOfExpr vars types expr = case expr of
  --Here we have the joy of parsing literals according to what pJS considers
  --true and false in a bool context.
  --However, since for now we only allow booleans in a bool context, we can
  --ignore this! TODO: correct this later.
  StringLit a _      -> return (types ! "string", (error "string vp NYI"))
  RegexpLit a _ _ _  -> return (types ! "RegExp", (error "regex  vp NYI"))
  NumLit a _         -> return (types ! "double", (error "numlit vp NYI"))
  IntLit a _         -> return (types ! "int", (error "intlit vp NYI"))
  --TODO: potential discrepancy in TS paper. T-True has
  --G |- true : Boolean; true, whereas in TS impl, true ends up having
  --type "true", not "Boolean".
  BoolLit a b        -> if b then return (TVal expr (types ! "bool"), VPTrue) 
                             else return (TVal expr (types ! "bool"), VPFalse)
  NullLit a          -> fail "NullLit NYI"
  ArrayLit pos exprs   -> do
    exprtypes' <- mapM (typeOfExpr vars types) exprs
    --TODO: see if we have to do anything else for array literal visible preds
    let exprtypes = map fst exprtypes'
    if length exprs == 0
      then fail $ "Empty array literals are not yet supported."
      else let (e1:erest) = exprtypes in do
             st <- foldM (\bestsofar newt -> maybe 
                           (fail $ "Array literal has no common supertype")
                           return
                           (bestSuperType vars types bestsofar newt))
                         e1 erest
             return (TApp pos (TId pos "Array") [st],(error "arraylit vp NYI"))
  ObjectLit pos props  -> let
      procProps [] = return []
      --TODO: object literals technically _could_ have numbers in
      --them, they just wouldn't be accessible with our
      --syntax. should we fail if we see them?
      procProps ((prop, giventype, expr):rest) = do
        --TODO: this might be refactorable into processRawEnv
        (exprtype, vp) <- typeOfExpr vars types expr
        let giventype' = case giventype of
                           Nothing -> exprtype
                           Just t -> t
        if not $ isSubType exprtype giventype' 
          then fail $ "expression " ++ (show expr) ++ 
                      " has type " ++ (show exprtype) ++ 
                      " which is not a subtype of declared type " ++ 
                      (show giventype')
          else do
            let thisprop = (Id pos (propToString prop), giventype')
            restprops <- procProps rest
            if elem (propToString prop) $ map (\((Id _ s),_) -> s) restprops
              then fail $ "duplicate property name in object literal: " ++ 
                          (propToString prop)
              else return (thisprop:restprops)
   in do propArray <- procProps props
         return (TObject pos propArray, error "objectlit vp NYI")

  ThisRef a          -> return $ (vars ! "this", VPId "this")
  VarRef a (Id _ s)  -> maybe (fail ("unbound ID: " ++ s)) 
                              (\t -> return (t, VPId s)) (M.lookup s vars)
  DotRef a expr id     -> do
    (exprtype, vp) <- typeOfExpr vars types expr
    --TODO: add an "objectContext" function that would convert string
    --to String, double to Number, etc.
    case exprtype of
      TObject _ props -> do
        maybe (fail $ "object " ++ (show exprtype) ++ 
                      " has no '" ++ (show id) ++ "' property")
              (\t -> return (t, error "dotref vp NYI"))
              (lookup id props)
      (TApp _ (TId _ "Array") [t_elt]) -> case lookup (unId id) arrayFields of
        Just t -> return (t,VPNone) -- TODO: is the VP correct?
        Nothing -> fail $ "array does not have a field called " ++ show id
      _ -> fail $ "dotref requires an object type, got a " ++ (show exprtype)
  BracketRef a contexpr keyexpr   -> do
    (conttype, vp) <- typeOfExpr vars types contexpr
    case conttype of
      TObject _ props -> do
        --TODO: once map-like things are done, add support for that here
         fail "no support for object[property] yet; use arrays only"
      (TApp _ (TId _ "Array") [t_elt]) -> do
        (keytype,vp) <- typeOfExpr vars types keyexpr
        case keytype <: (TId a "int") of
          True -> return (t_elt,VPNone) -- TODO: is this correct?
          False -> fail $ "indexing an array with a " ++ show keytype ++
                          " at " ++ show a
        
      _ -> fail $ "[] requires an object, got " ++ (show conttype)
  NewExpr a xcon xvars -> fail "newexpr NYI"
  
  --none of these expressions differentiate their type,
  --so their visible predicate is VPNone (the * in TS paper)
  PostfixExpr a op x -> do
    (xtype, vp) <- typeOfExpr vars types x
    ntype <- numberContext vars types xtype
    return (ntype, VPNone)
  
  PrefixExpr a op x -> do
    (xtype,vp) <- typeOfExpr vars types x
    case op of
      PrefixInc    -> novp $ numberContext vars types xtype
      PrefixDec    -> novp $ numberContext vars types xtype
      PrefixLNot   -> novp $ boolContext vars types xtype
      PrefixBNot   -> do ntype <- numberContext vars types xtype
                         if ntype == types ! "int"
                           then novp $ return $ types ! "int"
                           else fail $ "~ operates on integers, got " ++ 
                                       show xtype ++ " converted to " ++ 
                                       show ntype
      PrefixPlus   -> novp $ numberContext vars types xtype
      PrefixMinus  -> novp $ numberContext vars types xtype
      -- Void has been removed.  We are just sharing operator syntax with
      -- JavaScript.  It makes compiling to JavaScript much easier.
      PrefixVoid   -> fail "void has been removed"
      PrefixDelete -> novp $ return $ types ! "bool" --TODO: remove delete?
      --typeof DOES differentiate, somehow. will deal with it later.
      PrefixTypeof -> return (types ! "string", error "typeof vp NYI (imprtnt!")
     where
      novp m = m >>= \t -> return (t, VPNone)

  InfixExpr a op l r -> do
    --here we will do exciting things with || and &&, eventually
    (ltype,lvp) <- typeOfExpr vars types l
    (rtype,rvp) <- typeOfExpr vars types r
    let relation = 
          if (ltype == (types ! "string") && rtype == (types ! "string"))
            then return $ (types ! "bool", VPNone)
            else do
              numberContext vars types ltype
              numberContext vars types rtype
              return (types ! "bool", VPNone)
        logical = do
          boolContext vars types ltype
          boolContext vars types rtype
          return (types ! "bool", error "vp for logical infix NYI (important!)")
        numop = \requireInts alwaysDouble -> do
          ln <- numberContext vars types ltype
          rn <- numberContext vars types rtype
          if (ln == types ! "int" && rn == types ! "int") 
            -- we are given all integers
            then if alwaysDouble 
              then return (types ! "double",VPNone) --e.g. division
              else return (types ! "int",VPNone)    --e.g. +, -, *
            else if requireInts
              then fail $ "lhs and rhs must be ints, got " ++ 
                          show ln ++ ", " ++ show rn 
                          --e.g. >>, &, |
              else return (types ! "double",VPNone) --e.g. /
              
    case op of
      OpLT  -> relation
      OpLEq -> relation
      OpGT  -> relation
      OpGEq -> relation
      --TODO: maybe change OpIn to work for other types as well
      OpIn -> case rtype of 
                TObject{} -> return $ (types ! "bool", error "opin vp nyi")
                _         -> fail $ "rhs of 'in' must be an object, got " 
                                     ++ show rtype
      
      OpInstanceof -> case rtype of
        TFunc _ _ _ _ _ _ -> return $ (
           types ! "bool", error "instanceof vp NYI (important?)")
        _ -> fail $ "rhs of 'instanceof' must be constructor, got " 
                    ++ show rtype

      -- true == "1" will evaluate to true in tJS...
      -- these might have important visible predicates, too:
      OpEq        -> return (types ! "bool", error "opeq vp NYI")
      OpNEq       -> return (types ! "bool", error "opneq vp NYI")
      OpStrictEq  -> return (types ! "bool", error "opseq vp NYI")
      OpStrictNEq -> return (types ! "bool", error "opsneq vp NYI")
      
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
        -- from TDGTJ: If one operand is a string, the other is
        -- converted, and they are concatenated.  objects are
        -- converted to numbers or strings and then added or
        -- concatenated first valueOf is tried - if numbers result,
        -- then numbers are added then toString is tried. if toString
        -- returns a number, numbers are added.  if it returns a
        -- string, then strings are concatenated.  for now, let's just
        -- do strings or numbers:
        if ltype == (types ! "string") || rtype == (types ! "string") 
          then return $ (types ! "string", VPNone)
          else numop False False
  
  AssignExpr a op lhs rhs -> 
    -- TDGTJ: "In JavaScript, variables, properties of objects, and
    -- elements of arrays are lvalues." p62.
    -- TODO: see if any of these need special vps. guess: no.
    let rewrite infixop = typeOfExpr vars types 
                                    (AssignExpr a OpAssign lhs 
                                                (InfixExpr a infixop lhs rhs))
        procasgn = do
          (ltype, lvp) <- typeOfExpr vars types lhs
          (rtype, rvp) <- typeOfExpr vars types rhs
          case op of
            OpAssign -> if isSubType rtype ltype 
              then return (ltype, VPNone)
              else fail $ "in assignment, rhs " ++ (show rtype) ++ 
                          " is not a subtype of lhs " ++ (show ltype)
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
          VarRef{} -> procasgn  --TODO: add checks for readonly things
          DotRef{} -> procasgn
          BracketRef{} -> procasgn
          _ -> fail $ "lhs of assignment must be an lvalue: a variable," ++ 
                      " an object property, or an array element"
  
  CondExpr a c t e -> do
    (ctype,cvp) <- typeOfExpr vars types c 
    boolContext vars types ctype --boolContext will fail if something
                                 --goes wrong with 'c'
    (ttype,tvp) <- typeOfExpr (gammaPlus vars types cvp) types t
    (etype,evp) <- typeOfExpr (gammaMinus vars types cvp) types e
    maybe (fail $ "then and else of a ternary have no super type")
          (\t -> return (t, combpred cvp tvp evp))
          (bestSuperType vars types ttype etype)
    
  ParenExpr a x -> typeOfExpr vars types x
  ListExpr a exprs -> do
    typelist <- mapM (typeOfExpr vars types) exprs
    return $ last typelist


  CallExpr p fn typeArgs args -> do
    -- descend into function and arguments
    (fn_t,fn_vp) <- typeOfExpr vars types fn
    (actuals_t,args_vp) <- liftM unzip $ mapM (typeOfExpr vars types) args
    -- ensure that typeArgs do not have free variables
    let freeIds = S.difference (S.unions (map freeTIds typeArgs))
                               (S.fromList $ M.keys types)
    unless (S.null freeIds) $
      fail $ "type arguments at " ++ show p ++ " have free identifiers " ++
             show (S.toList freeIds) ++ "; env is " ++ show (M.keys types)
    -- instantiate the type of the function.  applyType will fail if there is
    -- an argument-count mismatch.
    instFn_t <- applyType fn_t typeArgs
    -- ensure that we have a function
    case deconstrFnType instFn_t of
      Nothing -> fail $ "applied expression is not a function at " ++ show p
      Just ([],formals_t,result_t,latentPred) -> do
        let (supplied_t,missing_t) = L.splitAt (length actuals_t) formals_t
        unless (length formals_t >= length actuals_t) $ do
          fail $ "function expects " ++ show (length formals_t) ++
                 " arguments, but " ++ show (length actuals_t) ++ 
                 " were supplied"
        let checkArg (actual,formal) = case actual <: formal of
              True -> return True
              False -> fail $ "expected " ++ show formal ++ "; received " ++ 
                              show actual ++ " at " ++ show p
        mapM_ checkArg (zip actuals_t supplied_t)
        let checkMissingArg actual = case actual of
              TNullable _ _ -> return True
              otherwise -> fail $ "non-null argument not supplied"
        mapM_ checkMissingArg missing_t

        --if we have a 1-arg func that has a latent pred, applied to a
        --visible pred of VID, then this is a T-AppPred        
        let isvpid (VPId _) = True
            isvpid _        = False
            a1vp            = args_vp !! 0
        if length formals_t == 1 
           && latentPred /= LPNone && isvpid a1vp
          then let (VPId id) = a1vp
                   (LPType ltype) = latentPred
                in return (result_t, VPType ltype id)
          else return (result_t, VPNone)
      Just (typeArgs,_,_,_) ->
        -- This should not happen:
        -- forall a b c. forall x y z . int -> bool
        fail $ "funciton type still has uninstantiated type variables"

  FuncExpr p formals type_ (BlockStmt p' body) -> case deconstrFnType type_ of
    Nothing -> fail $ "declared type on a function is not a function type"
    Just (typeArgs,args_t,result_t,latentP) -> do
      let freeIds = S.difference (freeTIds type_) (S.fromList $ M.keys types)
      unless (S.null freeIds) $
        fail $ "function at " ++ show p ++ " has free identifiers " ++
               show (S.toList freeIds) ++ " in its type"
      unless (length args_t == length formals) $
        fail $ "this function's type specifies " ++ (show $ length args_t) ++
               " arguments, but its definition has only " ++ 
               (show $ length formals) ++ " arguments"
      -- ignore var-arity
      let args = argEnv (zip (map unId formals) args_t) Nothing
      vars <- processRawEnv (M.union args vars) types (M.keys args) 
                            (globalEnv body)
      let tenvExt = M.fromList $ map (\s -> (s,TId p s)) typeArgs
      let types' = M.union tenvExt types
      doesAlwaysReturn <- allPathsReturn vars types' result_t 
                                         (BlockStmt p' body)
      unless (result_t == unitType || doesAlwaysReturn) $
        fail $ "All paths do not return, but function\'s return type is " ++
               show result_t
      typeCheckStmt vars types' (BlockStmt p' body)
      return (type_, error "vp for FuncExpr NYI")
  --just in case the parser fails somehow.
  FuncExpr _ _ _ _ -> fail "Function's body must be a BlockStmt" 

-- type check everything except return statements, handled in
-- typeOfExpr _ _ FuncExpr{}, and var declarations, handled in
-- whatever calls typeCheckStmt; both cases use Environment.hs .
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
     --fail "If with VP NYI!"
     (ctype,cvp) <- typeOfExpr vars types c
     boolContext vars types ctype
     results <- mapM (typeCheckStmt vars types) [t, e]
     return $ all id results
  IfSingleStmt pos c t -> do
     --fail "If with VP NYI!"
     (ctype,cvp) <- typeOfExpr vars types c
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
     (exprtype, evp) <- typeOfExpr vars types expr
     boolContext vars types exprtype     
     typeCheckStmt vars types statement
  DoWhileStmt pos statement expr -> do
     res <- typeCheckStmt vars types statement
     (exprtype, evp) <- typeOfExpr vars types expr
     boolContext vars types exprtype
     return res
   
  BreakStmt _ _ -> return True
  ContinueStmt _ _ -> return True
  LabelledStmt _ _ stmt -> typeCheckStmt vars types stmt
  
  --TODO: now that we have arrays and objects, we should be able to do
  --for in loops.
  ForInStmt _ (ForInVar (Id _ varname) vartype) inexpr body -> 
    fail "for..in loops NYI"
  ForInStmt _ (ForInNoVar (Id _ varname)) inexpr body -> 
    fail "for..in loops NYI"
    
  ForStmt a init test incr body -> do
    --var decls in the init are already processed by now
    let checkinit = case init of
          ExprInit expr -> (typeOfExpr vars types expr >> return True)
          _ -> return True
          
    checkinit
    --treat an empty test as "true"
    (testtype,vp) <- maybe (typeOfExpr vars types (BoolLit a True))
                           (typeOfExpr vars types) test
    boolContext vars types testtype
    --we don't care about the incr type, but it has to type-check
    --we use (types ! "bool") as filler so that 'maybe' can type properly
    (incrtype,ivp) <- maybe (typeOfExpr vars types (BoolLit a True))
                            (typeOfExpr vars types) incr
    typeCheckStmt vars types body
    
  ReturnStmt{} -> return True --handled elsewhere  
  VarDeclStmt{} -> return True -- handled elsewhere
  
  --TDGTJ p100: "expression may evaluate to a value of any type"
  --TODO: require catch clauses to declare the expected type. maybe restrict
  --      throw somehow so you can't just have anything in the catch clause...
  ThrowStmt pos expr -> do
    exprtype <- typeOfExpr vars types expr
    return True
  

{- Statements left over:

data Statement a
  = SwitchStmt a (Expression a) [CaseClause a]
  | ForInStmt a (ForInInit a) (Expression a) (Statement a)
  | TryStmt a (Statement a) {-body-} [CatchClause a] {-catches-}
      (Maybe (Statement a)) {-finally-}
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




