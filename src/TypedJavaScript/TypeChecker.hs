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

import TypedJavaScript.Prelude
import qualified Data.Map as M
import qualified Data.Set as S

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
  typeCheckStmt env coreTypeEnv [] (BlockStmt corePos stmts)
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
       ["string", "double", "int", "any", "bool", "Array"]) ++
  [("@global", globalObjectType), ("undefined", undefType)]

coreVarEnv :: Env
coreVarEnv = M.fromList $ [("this", coreTypeEnv ! "@global"),
                           ("undefined", coreTypeEnv ! "undefined")] ++
  --there's no way to distinguish 'int', so leave isInt in for now:
  [("isInt", makePred "int")] 
 where
  makePred s = (TFunc corePos Nothing [coreTypeEnv ! "any"] Nothing
                      (coreTypeEnv ! "bool") (LPType (coreTypeEnv ! s)))
-- TODO: deal with TApp, add syntax for defining them , etc.

-- check subtyping without any constraints.
a <:~ b = isSubType' a b
--temporary:
a <:  b = isSubType' a b

isSubType' :: Type SourcePos -> Type SourcePos -> Bool
--objects are invariant in their common field types
--TODO: verify that the 'case' here is well-founded, and that I'm not
--      doing something silly.
isSubType' (TObject _ props1) (TObject _ props2) =
  all (\(o2id@(Id _ o2propname), o2proptype) -> maybe
        False (\o1proptype -> case (o1proptype,o2proptype) of
                  --want to preserve this subtype among object props:
                  (TObject{},TObject{}) -> isSubType' 
                    o1proptype o2proptype
                  --but don't want subtype for other things:
                  _ -> o1proptype == o2proptype)     
              (lookup o2id props1))
      props2

isSubType' f2@(TFunc _ this2 req2 var2 ret2 lp2)  -- is F2 <= F1?
          f1@(TFunc _ this1 req1 var1 ret1 lp1) =
  let ist = isSubType'       
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

--the first of these cases works if both are unions; the second does not.
{- 
(x U y) <: (x U y)
--------------------------
first: x <: x U y and y <: x U y
-----------------------------------------
second: 
(x U y) <: x or (x U y) <: y
(x <: x and x <: y) or (x <: y and y <: y)
-}
isSubType' (TUnion _ ts) t = case ts of
  [] -> False
  _ -> all (\ti -> ti <:~ t) ts
isSubType' t (TUnion _ ts) = any (t <:~) ts
isSubType' _ (TId _ "any") = True -- TODO: O RLY?
isSubType' (TId _ "int") (TId _ "double") = True
isSubType' (TId _ x) (TId _ y) = x == y
isSubType' (TApp _ (TId _ "Array") args1) (TApp _ (TId _ "Array") args2) =
  args1 == args2
isSubType' (TApp _ c1 args1) (TApp _ c2 args2) = 
  c2 <:~ c1 &&
  (and $ zipWith (==) args1 args2) && --TODO: invariance better than subtyping?
  (length args1 == length args2)
isSubType'(TVal v1 t1) (TVal v2 t2) = v1 `eqLit` v2 && t1 <:~ t2
isSubType' (TVal _ t1) t2 = t1 <:~ t2
isSubType' (TForall ids1 tcs1 t1) (TForall ids2 tcs2 t2) = 
  ids1 == ids2 && tcs1 == tcs2 && t1 == t2

isSubType' (TIndex (TObject _ props1) (TVal (StringLit p s1) _) kn1)
          (TIndex (TObject _ props2) (TVal (StringLit _ s2) _) kn2) = 
  s1 == s2 && kn1 == kn2 && (do
    p1 <- lookup (Id p s1) props1
    p2 <- lookup (Id p s2) props2
    if p1 <:~ p2
      then return True
      else Nothing) /= Nothing
isSubType' (TIndex o1@(TObject _ props1) kt1@(TUnion _ s1s) kn1)
          (TIndex o2@(TObject _ props2) kt2@(TUnion _ s2s) kn2) = 
  kt1 == kt2 && kn1 == kn2 && 
    all (\s1 -> isSubType' (TIndex o1 s1 kn1) (TIndex o2 s1 kn2))
        s1s

isSubType' _ _ = False
-- check subtyping, taking constraints into account
isSubType :: [TypeConstraint] -> Type SourcePos -> Type SourcePos -> Bool
isSubType _ = isSubType'

--get the most specific supertype. best = most specific to save typing.
--used for array literals and ternary expressions
--TODO: this no longer returns Nothing                            
bestSuperType :: (Type SourcePos) -> (Type SourcePos) -> 
                 Maybe (Type SourcePos)

-- best super type of two objects is an object that has as
-- many properties as are in both:
bestSuperType (TObject pos1 props1) (TObject _ props2) = do
  --take everything that is in both objects. worst-case: {}.
  Just $ TObject (initialPos "bestSuperType") $ 
                 mapMaybe (\(prop1id, t1) -> liftM ((,) prop1id) 
                            (lookup prop1id props2 >>= bestSuperType t1)) 
                          props1 
--TODO: this no longer returns Nothing, so no need for it to return Maybe
bestSuperType t1 t2
 | (t1 == t2) = Just t1
 | (t1 <:~ t2) = Just t2
 | (t2 <:~ t1) = Just t1
 | otherwise = Just $ flattenUnion $ TUnion (typePos t1) [t1, t2] 

-- in pJS, anything can be used in a number and bool context without 
-- anything crashing.for now, we're making this a lot stricter:
numberContext :: (Monad m) => [TypeConstraint] -> 
                              (Type SourcePos) -> m (Type SourcePos)
numberContext cs t
  | isSubType cs t (TId corePos "double") = return t
  | otherwise = fail $ "expected a number (T <: double),  got " ++ show t

-- bool is also much freer in pJS. 
boolContext :: (Monad m) => Env -> Env -> [TypeConstraint] -> 
                            (Type SourcePos) -> m (Type SourcePos)
boolContext vars types cs t
    | isSubType cs t (types ! "bool") = return t
    | otherwise = fail $ "expected sub-type of bool, got " ++ show t

--take a union of many types and reduce it to the simplest one possible.
--Example: U(true, true, false, int, double, false) --> U(true, false, double)
--Example: U(U(true, int), false) --> U(true, false, int)
--So far, this just flattens the union
flattenUnion :: (Type SourcePos) -> (Type SourcePos)
flattenUnion (TUnion pos ts) = 
  case (foldl
         (\res t -> case t of
                      TUnion _ tocomb -> res ++ tocomb
                      regular -> res ++ [regular])
         [] ts) of
   [onet] -> onet
   noneormanyt -> TUnion pos noneormanyt

flattenUnion  t = t

-- returns whether or not all possible paths return
-- motivation: when checking functions with return values, at least
-- one of the statements must have all paths returning.
allPathsReturn :: (Monad m) => Env -> Env -> 
                  (Statement SourcePos) -> m Bool
allPathsReturn vars types stmt = case stmt of
  BlockStmt _ stmts -> do
    results <- mapM (allPathsReturn vars types) stmts
    return $ any id results 
  --TODO: could do some smarter occurrence-typing-like thing here:
  IfStmt _ _ t e -> do
    r1 <- allPathsReturn vars types t
    r2 <- allPathsReturn vars types e
    return $ r1 && r2
  IfSingleStmt _ _ t -> return False 
  SwitchStmt _ _ clauses -> do
    -- TODO: Switch: True if there is a default clause where all paths
    -- return, False otherwise
    fail "allPathsReturn, SwitchStmt, NYI" 
  WhileStmt _ _ body -> allPathsReturn vars types body
  DoWhileStmt _ body _ -> allPathsReturn vars types body
  ForInStmt _ _ _ body -> allPathsReturn vars types body
  ForStmt _ _ _ _ body -> allPathsReturn vars types body
  -- Try: true if all catches and/or the finally have a return
  TryStmt _ body catches mfinally -> fail "allPathsReturn, TryStmt, NYI" 
  ThrowStmt{} -> return True
  ReturnStmt _ _ -> return True
  -- any other statement does not return from the function, or contain return
  -- statements.
  _ -> return False

-- |If typeOfExpr returns a refined type (i.e. a 'TVal'), omit the refinement
-- and return the base type.
inferLocally :: (Monad m) => Env -> Env -> (Expression SourcePos) ->
                             m (Type SourcePos, VisiblePred SourcePos)
inferLocally vars types expr = do
  (exprtype, vp) <- typeOfExpr vars types [] expr
  case exprtype of
    (TVal _ t) -> return (t,vp)
    otherwise -> return (exprtype,vp)

-- given the current var and type environment, and a raw environment
-- representing new variable declarations from, for example, a
-- function, return the new variables environment or fail on type
-- error.  the variables initialized with expressions can reference
-- other variables in the rawenv, but only those declared above them.
-- the third argument is a list of IDs that this rawenv is forbidden
-- to override this starts off with just the function arguments, and
-- each added variable is added to the list
processRawEnv'' :: (Monad m) => Env -> Env -> [String] -> RawEnv -> m Env
processRawEnv'' vars types _ [] = return vars
processRawEnv'' vars types forbidden (entry@(Id _ varname,_,_):rest) = 
  if elem varname forbidden
    then fail $ "Can't re-define " ++ varname
    else case entry of
      (Id _ _, Nothing, Nothing) -> fail $ 
        "Invalid RawEnv contains var that has neither type nor expression"
      (Id _ varname, 
       Just t@(TApp _ (TId _ "Array") [elem_t]),
       Just (ArrayLit _ [])) ->
        processRawEnv'' (M.insert varname t vars) types (varname:forbidden)
                        rest
      (Id _ varname, Nothing, Just expr) -> do
        --local type inference
        (exprtype,vp) <- inferLocally vars types expr
        processRawEnv'' (M.insert varname exprtype vars) 
                      types (varname:forbidden) rest
      -- If a variable is declared with a type but is uninitialized,
      -- it must be nullable, ie have 'undefined' in its union, ie 
      -- have undefined be a sub-type of it
      (Id _ varname, Just vartype, Nothing) -> do
        let vartype' = vartype 
        case undefType <: vartype' of
          True  -> processRawEnv'' (M.insert varname vartype' vars) 
                                  types (varname:forbidden) rest
          False -> fail $ "unintialized variables must have nullable " ++
                          "types (suffix '?')"
      (Id _ varname, Just vartype, Just expr) -> do
        (exprtype,lp) <- typeOfExpr vars types [] expr
        let vartype' = vartype 
        seq vartype' $ 
          if not $ isSubType [] exprtype vartype'
            then fail $ "expression " ++ (show expr) ++ 
                        " has type " ++ (show exprtype) ++ 
                        " which is not a subtype of declared type " ++ 
                        (show vartype')
            else processRawEnv'' (M.insert varname vartype' vars) 
                               types (varname:forbidden) rest

-- |First add all locally defined functions to the environment.  This lets us
-- handle mutually recursive functions correctly.
-- 
-- Functions always have explicit type signatures.  Even if identifier naming a
-- function does not have a type signature, the function definition itself
-- has one.
processRawEnv' :: (Monad m) => Env -> Env -> [String] -> 
                  RawEnv -> RawEnv ->m Env
processRawEnv' vars types forbidden 
              (entry@(Id _ varname,t,_):rest) procced = case t of
  Just x -> case x of 
    TFunc{} -> processRawEnv' (M.insert varname x vars) types forbidden rest
                              (procced ++ [entry])
    _ -> processRawEnv' vars types forbidden rest (procced ++ [entry])
  _ -> processRawEnv' vars types forbidden rest (procced ++ [entry])
processRawEnv' vars types forbidden [] procced =
  processRawEnv'' vars types forbidden procced

--helper to hide the new function type of processRawEnv  
processRawEnv :: (Monad m) => Env -> Env -> [String] -> RawEnv -> m Env
processRawEnv vars types forbidden toproc = 
  processRawEnv' vars types forbidden toproc []

-- Helpers for occurrence typing, from TypedScheme paper
-- TODO: should occurrence typing have isSubType', or isSubType ?
restrict :: (Type SourcePos) -> (Type SourcePos) -> (Type SourcePos)
restrict s t
 | s <:~ t = s
 | otherwise = case t of
     TUnion pos ts -> flattenUnion $ 
                        TUnion pos (map (restrict s) ts)
     --TODO: make sure restrict is correct; this is different than
     --the typed scheme paper
     _ -> let rez = flattenUnion $
                      TUnion (typePos s) 
                             (filter (\hm -> isSubType' hm t)
                                     (case s of
                                        TUnion _ ts -> ts
                                        _ -> [s]))
           in case rez of 
                TUnion _ [] -> t
                _ -> rez

remove :: (Type SourcePos) -> (Type SourcePos) -> (Type SourcePos)
remove s t
 | s <:~ t = TUnion (typePos s) []
 | otherwise = case t of
     TUnion pos ts -> flattenUnion $ 
                        TUnion pos (map (remove s) ts)
     --TODO: make sure remove is correct; this is different than
     --the typed scheme paper
     _ -> flattenUnion $ 
            TUnion (typePos s) 
                   (filter (\hm -> not $ isSubType' hm t)
                           (case s of
                             TUnion _ ts -> ts
                             _ -> [s]))
     
--TODO: in TS, 'false' is false, and everything else is true. the same
--is not true in JS, so we have to think about how to handle gammaPlus
--and gammaMinus with VPIds.

gammaPlus :: Env -> (VisiblePred SourcePos) -> Env
gammaPlus g (VPType t x) = 
  M.insert x (restrict (g ! x) t) g
--remove all parts of x that are false:
gammaPlus g (VPId x) = M.insert x (remove (g ! x) 
                                          (TVal (BoolLit corePos False)
                                                (TId corePos "bool"))) g
--gammaPlus g (VPId x) = error "Gamma + VPId NYI" 
gammaPlus g (VPNot vp) = gammaMinus g vp
gammaPlus g _ = g

gammaMinus :: Env -> VisiblePred SourcePos -> Env
gammaMinus g (VPType t x) = 
  M.insert x (remove (g ! x) t) g
--gammaMinus g (VPId x) = M.insert x falseType g
--gammaMinus g (VPId x) = error "Gamma - VPId NYI" 
--restrict x to those parts of x that are false
--TODO: make sure this makes sense, as it's different than TS.
--      in particular, this might react badly with the changes
--      i made to 'restrict', since the following code:
--        x = 5;
--        if (x) {} else { x; }
--      the else branch will have 'x' being typed as 'false, which does
--      not really make sense!
gammaMinus g (VPId x) = M.insert x (restrict (g ! x) 
                                             (TVal (BoolLit corePos False)
                                                   (TId corePos "bool"))) g
gammaMinus g (VPNot vp) = gammaPlus g vp
gammaMinus g _ = g

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
typeOfExpr :: (Monad m) => Env -> Env -> [TypeConstraint] -> 
                          (Expression SourcePos) ->
                           m (Type SourcePos, VisiblePred SourcePos)
typeOfExpr vars types cs expr = case expr of
  --Here we have the joy of parsing literals according to what pJS considers
  --true and false in a bool context.
  --However, since for now we only allow booleans in a bool context, we can
  --ignore this! TODO: correct this later.
  StringLit a s      -> return (TVal expr (types ! "string"), 
                                if length s == 0 then VPFalse else VPTrue)
  RegexpLit a _ _ _  -> return (types ! "RegExp", 
                                VPTrue)
  NumLit a n         -> return (TVal expr (types ! "double"), 
                                if n==0 then VPFalse else VPTrue)
  IntLit a i         -> return (TVal expr (types ! "int"), 
                                if i==0 then VPFalse else VPTrue)
  --TODO: potential discrepancy in TS paper. T-True has
  --G |- true : Boolean; true, whereas in TS impl, true ends up having
  --type "true", not "Boolean".
  BoolLit a b        -> if b then return (TVal expr (types ! "bool"), VPTrue) 
                             else return (TVal expr (types ! "bool"), VPFalse)
  NullLit a          -> fail "NullLit NYI"
  ArrayLit pos exprs   -> do
    exprtypes' <- mapM (inferLocally vars types) exprs
    --TODO: see if we have to do anything else for array literal visible preds
    let exprtypes = map fst exprtypes'
    if length exprs == 0
      then fail $ "Empty array literals are not yet supported."
      else let (e1:erest) = exprtypes in do
             st <- foldM (\bestsofar newt -> maybe 
                           (fail $ "Array literal has no common supertype")
                           return
                           (bestSuperType bestsofar newt))
                         e1 erest
             return (TApp pos (TId pos "Array") [st],VPTrue)
  ObjectLit pos props  -> let
      procProps [] = return []
      --TODO: object literals technically _could_ have numbers in
      --them, they just wouldn't be accessible with our
      --syntax. should we fail if we see them?
      procProps ((prop, giventype, expr):rest) = do
        --TODO: this might be refactorable into processRawEnv
        (exprtype, vp) <- inferLocally vars types expr
        let giventype' = case giventype of
                           Nothing -> exprtype
                           Just t -> t
        if not $ exprtype <: giventype' 
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
         return (TObject pos propArray, VPTrue)

  ThisRef a          -> return $ (vars ! "this", VPId "this")
  VarRef a (Id _ s)  -> maybe (fail ("unbound ID: " ++ s)) 
                              (\t -> return (t, VPId s)) (M.lookup s vars)
  DotRef a expr id     -> do
    (exprtype, vp) <- typeOfExpr vars types cs expr
    --TODO: add an "objectContext" function that would convert string
    --to String, double to Number, etc.
    case exprtype of
      TObject _ props -> do
        maybe (fail $ "object " ++ (show exprtype) ++ 
                      " has no '" ++ (show id) ++ "' property")
              (\t -> return (t, error "dotref vp NYI"))
              (lookup id props)
      (TApp _ (TId _ "Array") [t_elt]) -> case lookup (unId id) arrayFields of
        Just t -> return (t, error "array dotref vp NYI") 
        Nothing -> fail $ "array does not have a field called " ++ show id
      _ -> fail $ "dotref requires an object type, got a " ++ (show exprtype)
  BracketRef a contexpr keyexpr   -> do
    (conttype, vp) <- typeOfExpr vars types cs contexpr
    case conttype of
      TObject _ props -> do
        (keytype,keyvp) <- typeOfExpr vars types cs keyexpr
        let lookitup s = case lookup s props of
              Nothing -> fail $ "object does not have property " ++ show s
              Just x -> return x
            checkkeytype kt = case kt of
              TId _ "string" -> fail "cannot index obj with generic string"
              TVal (StringLit _ s) (TId _ "string") -> do
                ptype <- lookitup (Id a s)
                return ptype
              TUnion _ ts -> do
                lawl <- mapM checkkeytype ts
                return $ lawl !! 0
        res <- checkkeytype keytype
        case keyvp of
          VPId keyname -> return (TIndex conttype keytype keyname, VPNone)
          _ -> fail "can only index objects with iterator variables"
      (TApp _ (TId _ "Array") [t_elt]) -> do
        (keytype,vp) <- typeOfExpr vars types cs keyexpr
        case keytype <: (TId a "int") of
          True -> return (t_elt,VPNone) -- TODO: is this correct?
          False -> fail $ "indexing an array with a " ++ show keytype ++
                          " at " ++ show a
        
      _ -> fail $ "[] requires an object, got " ++ (show conttype)
  NewExpr a xcon xvars -> fail "newexpr NYI"
  
  --none of these expressions differentiate their type,
  --so their visible predicate is VPNone (the * in TS paper)
  PostfixExpr a op x -> do
    (xtype, vp) <- typeOfExpr vars types cs x
    ntype <- numberContext cs xtype
    return (ntype, VPNone)
  
  PrefixExpr a op x -> do
    (xtype,vp) <- typeOfExpr vars types cs x
    case op of
      PrefixInc    -> novp $ numberContext cs xtype
      PrefixDec    -> novp $ numberContext cs xtype
      PrefixLNot   -> do
        t <- boolContext vars types cs xtype
        return (t, VPNot vp)
      PrefixBNot   -> do ntype <- numberContext cs xtype
                         if ntype == types ! "int"
                           then novp $ return $ types ! "int"
                           else fail $ "~ operates on integers, got " ++ 
                                       show xtype ++ " converted to " ++ 
                                       show ntype
      PrefixPlus   -> novp $ numberContext cs xtype
      PrefixMinus  -> novp $ numberContext cs xtype
      -- Void has been removed.  We are just sharing operator syntax with
      -- JavaScript.  It makes compiling to JavaScript much easier.
      PrefixVoid   -> fail "void has been removed"
      PrefixDelete -> novp $ return $ types ! "bool" --TODO: remove delete?
      --typeof DOES differentiate, somehow. will deal with it later.
      PrefixTypeof -> case vp of
        VPId i -> return (types ! "string", VPTypeof i)
        _      -> return (types ! "string", VPNone)
     where
      novp m = do
        t <- m
        return (t, VPNone)

  InfixExpr a op l r -> do
    --here we will do exciting things with || and &&, eventually
    (ltype,lvp) <- typeOfExpr vars types cs l
    (rtype,rvp) <- typeOfExpr vars types cs r
    let relation = 
          if (ltype == (types ! "string") && rtype == (types ! "string"))
            then return $ (types ! "bool", VPNone)
            else do
              numberContext cs ltype
              numberContext cs rtype
              return (types ! "bool", VPNone)
        logical = do
          boolContext vars types cs ltype
          boolContext vars types cs rtype
          return (types ! "bool", error "vp for logical infix NYI (important!)")
        numop = \requireInts alwaysDouble -> do
          ln <- numberContext cs ltype
          rn <- numberContext cs rtype
          if (ln <: (types ! "int") && rn <: (types ! "int"))
            -- we are given all integers
            then if alwaysDouble 
              then return (types ! "double",VPNone) --e.g. division
              else return (types ! "int",VPNone)    --e.g. +, -, *
            else if requireInts
              then fail $ "lhs and rhs must be ints, got " ++ 
                         show ln ++ ", " ++ show rn 
                          --e.g. >>, &, |
              else return (types ! "double",VPNone) --e.g. /
        equalityvp a b@(_,VPTypeof _) = equalityvp b a
        equalityvp (_,(VPTypeof i)) (TVal (StringLit _ s) (TId p "string"),_) = 
          case s of
            "number" -> VPType (TId p "double") i
            "undefined" -> VPType undefType i
            "boolean" -> VPType (TId p "bool") i
            "string" -> VPType (TId p "string") i
            "function" -> error "vp for typeof x == 'function' nyi"
            "object" -> error "vp for typeof x == 'object' nyi"
            _ -> VPNone
        equalityvp _ _ = VPNone
              
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
      OpNEq       -> return (types ! "bool", 
                             VPNot (equalityvp (ltype,lvp) (rtype,rvp)))
      OpStrictNEq -> return (types ! "bool", 
                             VPNot (equalityvp (ltype,lvp) (rtype,rvp)))
      OpEq        -> return (types ! "bool", equalityvp (ltype,lvp) (rtype,rvp))
      OpStrictEq  -> return (types ! "bool", equalityvp (ltype,lvp) (rtype,rvp))

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
        if ltype <: (types ! "string") || rtype <: (types ! "string") 
          then return $ (types ! "string", VPNone)
          else numop False False
  
  AssignExpr a op lhs rhs -> 
    -- TDGTJ: "In JavaScript, variables, properties of objects, and
    -- elements of arrays are lvalues." p62.
    -- TODO: see if any of these need special vps. guess: no.
    let rewrite infixop = typeOfExpr vars types cs
                                    (AssignExpr a OpAssign lhs 
                                                (InfixExpr a infixop lhs rhs))
        procasgn = do
          (ltype, lvp) <- typeOfExpr vars types cs lhs
          (rtype, rvp) <- typeOfExpr vars types cs rhs
          case op of
            OpAssign -> if isSubType cs rtype ltype
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
    (ctype,cvp) <- typeOfExpr vars types cs c 
    boolContext vars types cs ctype --boolContext will fail if something
                                 --goes wrong with 'c'
    (ttype,tvp) <- typeOfExpr (gammaPlus vars cvp) types cs t
    (etype,evp) <- typeOfExpr (gammaMinus vars cvp) types cs e
    maybe (fail $ "then and else of a ternary have no super type")
          (\t -> return (t, combpred cvp tvp evp))
          (bestSuperType ttype etype)
    
  ParenExpr a x -> typeOfExpr vars types cs x
  ListExpr a exprs -> do
    typelist <- mapM (typeOfExpr vars types cs) exprs
    return $ last typelist


  CallExpr p fn typeArgs args -> do
    -- descend into function and arguments
    (fn_t,fn_vp) <- typeOfExpr vars types cs fn
    (actuals_t,args_vp) <- liftM unzip $ mapM (typeOfExpr vars types cs) args
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
      Just ([],[],formals_t,result_t,latentPred) -> do
        let (supplied_t,missing_t) = splitAt (length actuals_t) formals_t
        unless (length formals_t >= length actuals_t) $ do
          fail $ "function expects " ++ show (length formals_t) ++
                 " arguments, but " ++ show (length actuals_t) ++ 
                 " were supplied"
        let checkArg (actual,formal) = case actual <: formal of
              True -> return True
              False -> fail $ "expected " ++ show formal ++ "; received " ++ 
                              show actual ++ " at " ++ show p
        mapM_ checkArg (zip actuals_t supplied_t)
        let checkMissingArg actual = case undefType <: actual of
              True  -> return True
              False -> fail $ "non-null argument not supplied"
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
      Just (typeArgs,_,_,_,_) ->
        -- This should not happen:
        -- forall a b c. forall x y z . int -> bool
        fail $ "funciton type still has uninstantiated type variables"

  FuncExpr p formals type_ (BlockStmt p' body) -> case deconstrFnType type_ of
    Nothing -> fail $ "declared type on a function is not a function type"
    -- TODO: Body must be checked with these constraints in place
    Just (typeArgs,constraints,args_t,result_t,latentP) -> do
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
      doesAlwaysReturn <- allPathsReturn vars types' (BlockStmt p' body)
      unless (result_t <: undefType || doesAlwaysReturn) $
        fail $ "All paths do not return, but function\'s return type is " ++
               show result_t
      typeCheckStmt (M.insert "return" result_t vars) types' []
                    (BlockStmt p' body)
      return (type_, VPTrue)
  --just in case the parser fails somehow.
  FuncExpr _ _ _ _ -> fail "Function's body must be a BlockStmt" 

-- type check everything except return statements, handled in
-- typeOfExpr _ _ FuncExpr{}, and var declarations, handled in
-- whatever calls typeCheckStmt; both cases use Environment.hs .
-- each statement might modify the environment - for example, if you have
-- an occurrence type in which you always return from the true branch,
-- so this returns a tuple of the new vars and types to use to type-check
-- all future statements in this block
typeCheckStmt :: (Monad m) => Env -> Env -> [TypeConstraint]
                 -> (Statement SourcePos) -> m (Env, Env)
typeCheckStmt vars types cs stmt = case stmt of 
  BlockStmt pos stmts -> let
      tc v t [] = return (v, t)
      tc v t (first:rest) = do
        (v', t') <- typeCheckStmt v t cs first
        tc v' t' rest
    in tc vars types stmts

  EmptyStmt pos -> return (vars, types)
  ExprStmt  pos expr -> do
    typeOfExpr vars types cs expr
    return (vars, types)

  IfStmt pos c t e -> do 
     (ctype,cvp) <- typeOfExpr vars types cs c
     boolContext vars types cs ctype
     result1 <- typeCheckStmt (gammaPlus vars cvp) types cs t
     result2 <- typeCheckStmt (gammaMinus vars cvp) types cs e
     --TODO: we might want to use result1 and result2 somehow
     apt <- allPathsReturn vars types t
     ape <- allPathsReturn vars types e
     case (apt, ape) of
       --TODO: not sure about the (True, True) case:
       (True, True)   -> return (gammaMinus (gammaPlus vars cvp) cvp, types)
       (True, False)  -> return (gammaMinus vars cvp, types)
       (False, True)  -> return (gammaPlus vars cvp, types)
       (False, False) -> return (vars, types)
     
  IfSingleStmt pos c t -> do
     (ctype,cvp) <- typeOfExpr vars types cs c
     boolContext vars types cs ctype
     result <- typeCheckStmt (gammaPlus vars cvp) types cs t
     --TODO: we might want to use result itself somehow
     apt <- allPathsReturn vars types t
     if apt
       then return (gammaMinus vars cvp, types)
       else return (vars, types)

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
     (exprtype, evp) <- typeOfExpr vars types cs expr
     boolContext vars types cs exprtype     
     typeCheckStmt vars types cs statement
  DoWhileStmt pos statement expr -> do
     res <- typeCheckStmt vars types cs statement
     (exprtype, evp) <- typeOfExpr vars types cs expr
     boolContext vars types cs exprtype
     return res
   
  BreakStmt _ _ -> return (vars, types)
  ContinueStmt _ _ -> return (vars, types)
  LabelledStmt _ _ stmt -> typeCheckStmt vars types cs stmt
  
  ForInStmt p (ForInNoVar _) _ _ -> fail "for in without a var NYI"
  ForInStmt p invar' inexpr body -> do
    (intype, invp) <- typeOfExpr vars types cs inexpr
    case intype of 
      TObject _ props -> if lookup (Id p "@[]") props /= Nothing
        then fail "for in array nyi"
        else let
            gv (ForInVar (Id _ varname)) = varname
            gv (ForInNoVar (Id _ varname)) = varname
            invar = gv invar'
            invart = TUnion p $ map (\(Id _ s,_) -> TVal (StringLit p s)
                                                         (types ! "string"))
                                    props        
         in typeCheckStmt (M.insert invar invart vars) types cs body
      _ -> fail $ "Can only 'for in' with an object type, given " ++ show intype
    
  ForStmt a init test incr body -> do
    --var decls in the init are already processed by now
    let checkinit = case init of
          ExprInit expr -> (typeOfExpr vars types cs expr >> return True)
          _ -> return True
          
    checkinit
    --treat an empty test as "true"
    (testtype,vp) <- maybe (typeOfExpr vars types cs (BoolLit a True))
                           (typeOfExpr vars types cs) test
    boolContext vars types cs testtype
    --we don't care about the incr type, but it has to type-check
    --we use (types ! "bool") as filler so that 'maybe' can type properly
    (incrtype,ivp) <- maybe (typeOfExpr vars types cs (BoolLit a True))
                            (typeOfExpr vars types cs) incr
    typeCheckStmt vars types cs body

  ReturnStmt p retexpr' -> case M.lookup "return" vars of
    Nothing -> fail $ "return stmt found in a non-function"
    Just rettype -> case retexpr' of
  -- return; means we are returning undefined. If the return type is nullable,
  -- that is just fine.
      Nothing -> if undefType <: rettype
        then return (vars, types)
        else fail $ "returning nothing when expected rettype is " ++ 
                    show rettype
      Just retexpr -> do
        (rt,rvp) <- typeOfExpr vars types cs retexpr
        if rt <: rettype
          then return (vars, types)
          else fail $ "returning type " ++ show rt ++ " which is not a " ++
                      "sub-type of the expected return type, " ++ show rettype

  VarDeclStmt{} -> return (vars, types) -- handled elsewhere
  
  --TDGTJ p100: "expression may evaluate to a value of any type"
  --TODO: require catch clauses to declare the expected type. maybe restrict
  --      throw somehow so you can't just have anything in the catch clause...
  ThrowStmt pos expr -> do
    exprtype <- typeOfExpr vars types cs expr
    return (vars, types)
  

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




