module BrownPLT.TypedJS.TypeCheck
  ( typeCheck
  , typeCheckExpr
  , withInitEnv
  ) where

import BrownPLT.TypedJS.Infrastructure
import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.LocalVars
import BrownPLT.TypedJS.RuntimeAnnotations
import BrownPLT.TypedJS.TypeDefinitions
import BrownPLT.TypedJS.TypeTheory
import BrownPLT.TypedJS.PrettyPrint
import BrownPLT.TypedJS.Syntax
import BrownPLT.TypedJS.Unification
import qualified Data.Map as M
import qualified Data.Set as S
import BrownPLT.TypedJS.PreTypeCheck
import Control.Monad.Reader
import Control.Monad.Error
import System.IO.Unsafe

--info for stmt, indicating whether we're in a constructor, or
--a function, and containing relevant data

data FunctionInfo 
 = ToplevelInfo --no necessary info here 
 | FunctionInfo Type --return type
 --constructor has:
 --expected this type (right of arrow)
 --set of fields in this that have not yet been initialzed.
 --unless the set is empty, the only allowed instructions are assignments to
 --'this'
 | ConstructorInfo Type (S.Set String) 
 

runtimeEnv :: TypeCheck (Map String RuntimeTypeInfo)
runtimeEnv = do
  m <- envMap
  return (M.map runtime m)


unAssignOp :: AssignOp -> InfixOp
unAssignOp op = case op of
  OpAssignAdd -> OpAdd
  OpAssignSub -> OpSub
  OpAssignMul -> OpMul
  OpAssignDiv -> OpDiv
  OpAssignMod -> OpMod
  OpAssignLShift -> OpLShift
  OpAssignSpRShift -> OpSpRShift
  OpAssignZfRShift -> OpZfRShift
  OpAssignBAnd -> OpBAnd
  OpAssignBXor -> OpBXor
  OpAssignBOr -> OpBOr
  OpAssign -> error "TypeCheck.hs : unAssignOp received OpAssign"


unLVal :: LValue SourcePos -> Expression SourcePos
unLVal (LVar p x) = VarRef p (Id p x)
unLVal (LDot p e x) = DotRef p e (Id p x)
unLVal (LBracket p e1 e2) = BracketRef p e1 e2


-- | @implicitlyPack  (actualTy, declaredTy, expr)@
--
-- @pack X in pack Y in e@, where @e :: t@, has the type 
-- @exists X . exists Y . t@
--
-- e :: s and t = exists X . exists Y . t
--
-- pack X in pack Y in e has the type exists X . exists Y . t
-- pack Y in e has the type exists Y . t
implicitlyPack :: (Type, Type, Expression SourcePos)
               -> TypeCheck (Expression SourcePos, Type)
implicitlyPack (actualTy, declaredTy, e) = case (actualTy, declaredTy) of
  (TExists _, TExists _) -> return (e, actualTy)
  (_, TExists ty) -> freshTVar $ \x -> do
    let ty' = openType (TId x) ty
    (e, actualTy) <- implicitlyPack (actualTy, ty', e)
    s <-  accumError "implicitly packing" $ unify actualTy ty'
    let e' = PackExpr (initialPos "implicit pack")
                      e (subst s (TId x)) (subst s (TExists ty))
    return (e', subst s $ TExists ty)
  otherwise -> return (e, actualTy)


openUniversals :: Type -> TypeCheck ([String], Type)
openUniversals (TForall ty) = freshTVar $ \x -> do
  (xs, ty') <- openUniversals (openType (TId x) ty)
  return (x:xs, ty')
openUniversals ty = return ([], ty)

-- |JavaScript's function call syntax is overloaded for three kinds of
-- function invocations.  These are @obj.method(arg, ...)@,
-- @obj[method](arg, ...)@ and @func(arg, ...)@.
--
-- This function returns the type of the object (@Window:{}@ in the first case,
-- @obj@ in the latter cases) and the type of the function.
callObj :: Expression SourcePos -> TypeCheck (Type, Type)
callObj e = case e of
  DotRef p obj (Id _ method) -> do
    objTy <- expr obj
    -- Based on the DotRef case of expr.
    r <- projBrand objTy
    case r of
      Just (brand, tyArgs) -> do
        prototypeTy <- brandType brand tyArgs
        fieldTy <- projFieldType (TIntersect objTy prototypeTy) method
        case fieldTy of
          Just t -> return (objTy, t)
          Nothing -> fatalTypeError p $ printf
            "%s\ndoes not have the field %s" (renderType objTy) method
      Nothing -> fatalTypeError p $ printf
        "expected an object with a field %s, got\n%s" method (renderType objTy)
  BracketRef p obj method -> 
    error "calling BracketRef NYI"
  otherwise -> do
    objTy <- brandType "Window" []
    funcTy <- expr e
    return (objTy, funcTy)
    


ok :: TypeCheck ()
ok = return ()


brandTVars :: SourcePos
           -> String -- ^brand
           -> TypeCheck [String]
brandTVars p brand = do
  let f t = case t of
        TNamedForall x u -> x:(f u)
        TConstr{} -> []
        otherwise -> catastrophe p $ printf "quantifyExternalFieldType got %s"
          (renderType t)
  constrTy <- getBrand brand
  return (f constrTy)


-- |Calculates the type of a local variable that does not have a type
-- type annotation.  Extends the environment with the type of the variable.
-- Expects the environment to contain the preceding local variables.
--
-- Although local variables are visible to each other, the only way to have 
-- recursive definitions is with functions.  However, functions have explicit 
-- type annotations, even if the variable itself does not have one.  Anything 
-- else counts as a define-before-use error.
calcType :: TypeCheck a
         -> LocalDecl
         -> TypeCheck a
calcType m decl = case decl of
  DeclType x t -> do
    u <- desugarType noPos t
    extendEnv x (lcType u) m
  DeclExpr x (FuncExpr _ _ t _) -> do
    u <- desugarType noPos t
    extendEnv x (lcType u) m
  DeclExpr x e -> do
    t <- expr e
    extendEnv x t m
  DeclField brand field (FuncExpr _ _ ty _) ->  do
    tVars <- brandTVars noPos brand
    ty <- bindTVars tVars $ desugarType noPos ty
    extendBrand brand field (lcType ty)
    m
  DeclField brand field e -> do
    t <- expr e
    extendBrand brand field t
    m
  DeclUnpack x tVars e -> bindTVars tVars $ do
    t <- expr e
    let unpack ty tVar = case ty of
          TExists s -> return (openType (TId tVar) s)
          otherwise -> fatalTypeError noPos $ printf
            "RHS has type %s, but the type variables specified were %s"
            (renderType t) (show tVars)
    s <- foldM unpack t tVars
    extendEnv x s m
  DeclConstr brand ty -> do
    newBrand brand (getConstrObj ty) (TObject "Object" [] [])
    ty <- desugarType noPos ty
    extendEnv brand (lcType ty) m
--   DeclConstr brand ty -> case ty of
--     TConstr argTys initTy objTy -> do
--       newBrand brand objTy (TObject "Object" [] [])
--       extendEnv brand ty m
--     TForall
--     
--     otherwise -> error $ printf
--       "calcType: unrecognized DeclConstr %s %s" brand (show ty)

calcTypes :: [LocalDecl]
          -> TypeCheck a
          -> TypeCheck a
calcTypes binds m = foldr (flip calcType) m binds


field :: (Prop SourcePos,  Expression SourcePos)
      -> TypeCheck Field
field f = case f of
  (PropId p (Id _ x), e) -> do
    ty <- expr e
    return (x, False, ty) -- fields are mutable by default
  (PropString p str, e) -> do
    ty <- expr e
    return (str, False, ty)
  (PropNum p n, e) -> do
    ty <- expr e
    return (show n, False, ty)
         
 
numericOp :: SourcePos -> Expression SourcePos
          -> Type -> Type -> Bool -> Bool -> TypeCheck Type
numericOp loc e lhs rhs requireInts returnDouble = do
  result <- case returnDouble of
    True -> return $ intersectType doubleType numberObjectType
    False -> do
      r <- isSubtype lhs intType
      case r of
        True -> return rhs
        False -> return lhs
  case requireInts of
    True -> do
      r <- isSubtype lhs intType +++ isSubtype rhs intType
      unless r $
        fatalTypeError loc $ printf 
          "operator expects Int arguments, given %s and %s in expression %s" 
          (renderType lhs) (renderType rhs) (renderExpr e)
      return result
    False -> do
      r <- isSubtype lhs (TUnion doubleType intType) +++ 
           isSubtype rhs (TUnion doubleType intType)
      unless r $
        fatalTypeError loc $ printf 
          "operator expects double/int arguments, given %s and %s" 
          (renderType lhs) (renderType rhs)
      return result


-- Fails if the l-value is a union in an enclosing scope
lvalue :: LValue SourcePos
       -> TypeCheck Type
lvalue lv = case lv of
  LVar p x -> do
    (s, n) <- lookupScopeEnv p x
    m <- scopeEnv
    case n < m of
      -- x is a variable in an enclosing scope.
      True -> do
        t <- lookupEnv p x
        case t of
          TUnion _ _ -> fatalTypeError p $ printf 
            "cannot assign to union types in an enclosing scope"
          otherwise -> return t
      -- x is a local variable.  The local scope may make assumptions about
      -- its runtime type.
      False -> lookupEnv p x
  LDot p obj f -> do
    tObj <- expr obj
    case tObj of
      TObject brand tyArgs fields -> do
        fields' <- intersectBrand brand tyArgs
        case fieldType f (overrideFields fields fields') of
          Just (s, False)  -> return s
          Just (s, True) -> do
            fatalTypeError p $ printf "the field %s is readonly" f
          Nothing -> do
            fatalTypeError p $ printf 
              "object %s\ndoes not have the field %s\n%s" 
              (renderType tObj) f
              (show $ overrideFields fields fields')
      otherwise -> do
        fatalTypeError p $ printf "expected object"
  LBracket p arr ix -> do
    tyArr <- expr arr >>= projType isArrayType
    tyIx <- expr ix >>= projType isIntType
    case (tyArr, tyIx) of
      (Just (TApp "Array" [tyElt]), Just _) -> return tyElt
      otherwise -> fatalTypeError p "expected array / integer index"


expr :: Expression SourcePos 
     -> TypeCheck Type
expr e = case e of
  StringLit _ _ -> return stringType
  RegexpLit _ _ _ _ -> fail "RegexpLit NYI"
  NumLit p _ -> return $ intersectType doubleType numberObjectType
  IntLit p _ -> return $ intersectType intType numberObjectType
  BoolLit _ _ -> return boolType
  NullLit _ -> fail "NullLit NYI"
  ThisRef p -> lookupEnv p "this"

  --empty array literal assignment:
  AssignExpr p OpAssign lhs (ArrayLit _ []) -> do
    s <- lvalue lhs
    moan <- projType isArrayType s
    case moan of
      Just (TApp "Array" [r]) -> return $ intersectType (TApp "Array" [r]) 
                  (openType r freeArrayType)
      Nothing -> fatalTypeError p "assigning empty array lit to non-array var"
  ArrayLit p [] -> fatalTypeError p $ printf
    "empty array literals must be bound to identifiers with type annotations."

  ArrayLit p (e1:es) -> do
    t1 <- expr e1
    ts <- mapM expr es
    let t = foldr unionType t1 ts
    return $ intersectType (TApp "Array" [t]) (openType t freeArrayType)
  VarRef p (Id _ x) -> lookupEnv p x
  DotRef p e (Id _ x) -> do
    objTy <- expr e
    r <- projBrand objTy
    case r of
      Just (brand, tyArgs) -> do
        prototypeTy <- brandType brand tyArgs
        fieldTy <- projFieldType (TIntersect objTy prototypeTy) x
        case fieldTy of
          Just t -> return t
          Nothing -> fatalTypeError p $ printf
            "%s\ndoes not have the field %s\n%s" (renderType objTy) x
             (renderType (TIntersect objTy prototypeTy))
 

      Nothing -> fatalTypeError p $ printf
        "expected an object with a field %s, got\n%s" x (renderType objTy)
  BracketRef p e1 e2 -> do
    t1 <- expr e1 >>= projType isArrayType
    t2 <- expr e2 >>= projType isIntType
    case (t1, t2) of
      (Just (TApp "Array" [x]), Just (TApp "Int" [])) -> return x
      otherwise -> fatalTypeError p "expected array or integer index"
  PrefixExpr p op e -> do
    t <- expr e
    isDoubleSubtype <- isSubtype t doubleType
    case op of
      PrefixLNot -> return boolType
      PrefixBNot | isDoubleSubtype -> return t
      PrefixPlus | isDoubleSubtype -> return t
      PrefixMinus | isDoubleSubtype -> return t
      PrefixTypeof -> return stringType
      PrefixVoid -> fail "PrefixVoid NYI"
      PrefixDelete -> fail "PrefioxDelete NYI"
      otherwise -> fail $ printf "%s applied to an expression of type %s"
                                        (show op) (renderType t)
  InfixExpr p op e1 e2 -> do
    lhs <- expr e1
    rhs <- expr e2
    let cmp = do
          r <- (isSubtype lhs stringType +++ isSubtype rhs stringType) -=-
               (isSubtype lhs doubleType +++ isSubtype rhs doubleType)
          unless r $
            fatalTypeError p $ printf 
              "%s may only be applied to numbers and strings; arguments \
              \ have types\n%s\nand\n%s" (show op) (renderType lhs)
              (renderType rhs)
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
      OpAdd -> do
        r <- isSubtype lhs stringType
        case r of
          True -> return stringType
          False -> do 
            r <- isSubtype rhs stringType
            case r of
              True -> return stringType
              False -> numericOp p e lhs rhs False False          
      OpLAnd -> canonicalUnion rhs boolType
      OpLOr -> canonicalUnion lhs rhs
  CondExpr p e1 e2 e3 -> do
    t1 <- expr e1
    t2 <- expr e2
    t3 <- expr e3
    canonicalUnion t2 t3
  -- postfix/prefix increment/decrement
  UnaryAssignExpr p op lv -> do
    t <- lvalue lv
    r <- isSubtype t doubleType
    case r of
      True -> return t
      False -> do
        fatalTypeError p $ printf
          "incrementing/decrementing an expression of type %s" (renderType t)

  AssignExpr p OpAssign lhs rhs -> do
    t <- expr rhs
    s <- lvalue lhs
    r <- isSubtype t s
    case r of
      True -> return t
      False -> do
        fatalTypeError p $ printf
          "error assigning to local variable of type %s, given an \
          \expression of type %s" (renderType s) (renderType t)
  AssignExpr p op lhs rhs -> expr $
    AssignExpr p OpAssign lhs (InfixExpr p (unAssignOp op) (unLVal lhs) rhs)
  ParenExpr _ e -> expr e
  ListExpr p [] -> catastrophe p "empty ListExpr"
  ListExpr p es -> 
    foldM (\_ e -> expr e) undefined es -- type of the last expression
  ObjectLit p fields -> do
    let unProp p = case p of
          PropId _ (Id _ x) -> x
          PropString _ x -> x
          PropNum _ n -> show n
    let names = map (unProp.fst) fields
        
    -- Confirmed in Rhino that this is not a syntax error in JavaScript.
    unless (length fields == length (nub names)) $
      fatalTypeError p "duplicate field names"
    ts <- mapM field fields
    desugarType p (TObject "Object" [] ts) -- rearrange fields
  NewExpr p constr args -> do
    constrTy <- expr constr
    argTys <- mapM expr args
    let check constrTy = case constrTy of
          TConstr brand formalTys _ objTy -> do
            argsMatch <- areSubtypes argTys formalTys
            unless argsMatch $ fatalTypeError p $ printf
              "constructor expects\n%s\n\nbut it received\n%s"
                (concat $ intersperse ",\n" $ map renderType formalTys)
                (concat $ intersperse ",\n" $ map renderType argTys)
            return objTy
          otherwise -> fatalTypeError p $ printf
            "'new' expected an a constructor; received\n%s" 
            (renderType constrTy)
    case constrTy of
      TConstr{} -> check constrTy
      otherwise -> do
        (tVars, ty) <- openUniversals constrTy
        case ty of
          TConstr brand formalTys _ _ -> do
            s <- accumError (show p) $ unifyList formalTys argTys
            let tyApp e tVar =
                  TyAppExpr (initialPos "implicit type application at new")
                            e
                            (subst s (TId tVar))
            constrTy <- expr (foldl tyApp constr tVars)
            check constrTy
          otherwise -> fatalTypeError p $ printf
            "'new' expected an a constructor; received\n%s" 
            (renderType constrTy)
  CallExpr p f ts args -> do
    (objTy, fTy) <- callObj f
    argTys <- mapM expr args
    let check fTy = case fTy of
          TArrow thisTy (ArgType argTypes optArgType) resultType -> do
            unless (length args == length argTypes) $ 
              fatalTypeError p $ printf 
                "function expects %s arguments but %s were supplied"
                (show $ length argTypes) (show $ length args)
            args <- accumError (show p) $ liftM (map fst) $ 
              mapM implicitlyPack (zip3 argTys argTypes args)
            argTys <- mapM expr args
            argsMatch <- liftM and (mapM (uncurry isSubtype) 
                                   (zip argTys argTypes))
            unless argsMatch $
              fatalTypeError p $ printf
                "argument type mismatch, expected\n%s\n received\n%s"
                (concat $ intersperse ", " $ map renderType argTypes)
                (concat $ intersperse ", " $ map renderType argTys)
            thisMatch <- isSubtype objTy thisTy
            unless thisMatch $ fatalTypeError p $ printf 
              "function expects the type of this to be\n%s\ncalled with\n%s"
              (renderType thisTy) (renderType objTy)
            return resultType
          otherwise -> do
            fatalTypeError p $ printf 
              "expected a function; expression has type\n%s"
              (renderType fTy)
    case fTy of
      TArrow{} -> check fTy
      otherwise -> do
        (tVars, ty) <- openUniversals fTy
        case ty of
          TArrow _ (ArgType formalTys Nothing) _ -> do
            s <- accumError (show p) $ unifyList argTys formalTys
            let tyApp e tVar =
                  TyAppExpr (initialPos "implicit TyAppExpr")
                            e
                            (subst s (TId tVar))
            fTy <- expr (foldl tyApp f tVars)
            check fTy
          otherwise -> fatalTypeError p $ printf
            "expected a function; expression has type %s" (renderType ty)
  FuncExpr p args t body -> do
    let (qtVars, t') = unForall t
    bindTVars qtVars $ do
      t <- desugarType p t'
      case t of
        TArrow thisType (ArgType argTypes optArgType) resultType -> do
          unless (length args == length (nub $ map unId args)) $
            fatalTypeError p "function argument names must be unique"
          unless (length args == length argTypes) $
            fatalTypeError p "argument count mismatch"
          unless (allPathsReturn body) $ do
            (isSubtype undefType resultType -=-
             fatalTypeError p "all control paths in function to not return a \
                              \result")
            ok
          nestEnv $ extendsEnv (zip (map unId args) argTypes) $ 
            extendEnv "this" thisType $ do
            rtEnv <- runtimeEnv
            localEnv <- declaredLocalTypes (map unId args) body 
            body <- runtimeAnnotations rtEnv localEnv body
            (vars, tvars) <- localVars (map unId args) body
            -- Calculating types affects the brand store.  Scope the 
            -- effects and recompute in the calculated environment.
            env <- tempBrandStore $ bindTVars tvars $ calcTypes vars $ ask
            local (const env) $ stmt (FunctionInfo resultType) body
            return (foldr (\x t -> TForall (closeType x t)) t qtVars)
        -- annotation on the function is not a function type
        otherwise -> do
          fatalTypeError p $ printf "expected a function type, received %s" 
                               (renderType t)
          return t
  AnnotatedVarRef p rt x 
    | S.null rt -> lookupEnv p x -- provably unreachable
    | otherwise -> do
        s <- lookupEnv p x
        u <- static rt s   
        
        case u of
          Just t -> return t --seq abba $ return t
          Nothing -> catastrophe p $ 
            printf "%s :: %s is inconsistent with the runtime type %s" 
                   x (renderType s) (show rt)
  PackExpr p e c t -> do
    t <- desugarType p t
    c <- desugarType p c
    case t of
      TExists t' -> do
        s <- expr e
        isSt <- isSubtype s (openType c t')
        case isSt of
          True -> return (TExists t')
          False -> do
            fatalTypeError p $ printf "expected\n%s\nto have the shape\n%s"
              (renderType s) (renderType (openType c t'))
      otherwise -> fatalTypeError p $ printf
        "expected existential type to pack, received %s" (renderType t)
  TyAppExpr p e t -> do
    t <- desugarType p t
    s <- expr e
    case s of
      TForall s' -> return (openType t s')
      otherwise -> fatalTypeError p $ 
        printf "expected a quantified type, received %s" (renderType s)
        

stmt :: FunctionInfo -- ^ are we at toplevel, in function, or in constr?
     -> Statement SourcePos
     -> TypeCheck ()
stmt finfo s = case s of
  BlockStmt _ ss -> mapM_ (stmt finfo) ss
  EmptyStmt _ -> ok
  ExprStmt _ e -> expr e >> ok
  IfStmt _ e s1 s2 -> do
    expr e -- we permit non-boolean tests
    stmt finfo s1
    stmt finfo s2
  IfSingleStmt _ e s -> do
    expr e -- we permit non-boolean tests
    stmt finfo s
  SwitchStmt _ e cases -> do
    expr e
    let case_ (CaseClause _ e ss) = do
          expr e
          mapM_ (stmt finfo) ss
        case_ (CaseDefault _ ss) =
          mapM_ (stmt finfo) ss
    mapM_ case_ cases
  WhileStmt _ e s -> do
    expr e
    stmt finfo s
  DoWhileStmt _ s e -> do
    stmt finfo s
    expr e
    ok
  BreakStmt _ _ -> ok
  ContinueStmt _ _ -> ok
  LabelledStmt _ _ s -> stmt finfo s
  ForInStmt _ init e s -> fail "ForInStmt NYI"
  ForStmt _ init test incr s -> do
    case init of
      NoInit -> ok
      VarInit decls -> mapM_ (decl) decls
      ExprInit e -> expr e >> ok
    case test of
      Nothing -> ok
      Just e -> expr e >> ok
    case incr of
      Nothing -> ok
      Just e -> expr e >> ok
    stmt finfo s
  TryStmt _ body catches finally -> fail "TryStmt NYI"
  ThrowStmt _ e -> expr e >> ok
  ReturnStmt p ret -> case finfo of
    ToplevelInfo -> fatalTypeError p $ printf 
      "return used at the top level"
    ConstructorInfo{} -> do 
      --you can have blank 'return's in constructors
      case ret of
        Nothing -> ok
        Just _ -> fatalTypeError p $ printf
          "non-empty return used in a constructor"
    FunctionInfo returnType -> case ret of
      Nothing -> do
        r <- isSubtype undefType returnType
        case r of
          True -> ok
          False -> fatalTypeError p $ printf 
                     "empty return, expected %s" 
                     (renderType returnType)
      Just e -> do
        t <- expr e
        (e, _) <- implicitlyPack (t, returnType, e)
        t <- expr e
        r <- isSubtype t returnType
        case r of
          True -> ok
          False -> fatalTypeError p $ printf 
            "statement returns\n%s\nExpected\n%s"
                     (renderType t) (renderType returnType)
  VarDeclStmt p decls -> mapM_ (decl) decls

--returns a set unchecked fieldasgns
constructorInit :: SourcePos
                -> Type
                -> S.Set String
                -> [ConstrFieldAsgn SourcePos]
                -> TypeCheck [ConstrFieldAsgn SourcePos]
constructorInit p (TObject{}) fieldsLeft [] = do
  if S.null fieldsLeft then return [] else 
    fatalTypeError p $ printf 
      "fields %s left uninitialized at end of constructor init block" 
      (show $ S.toList fieldsLeft)
constructorInit p (rtt@(TObject brand tyArgs fields)) fieldsLeft 
                (asgns@((ConstrFieldAsgn p' n x):as)) = if S.null fieldsLeft
  then return asgns 
  else do
    --if we're done initing all fields, can just stop and remove
    --restrictions on the remaining asgns.
    --otherwise:
    
    fields' <- intersectBrand brand tyArgs
    s <- case fieldType n (overrideFields fields fields') of
           --even read-only stuff can be set here:
           Just (s, _) -> return s
           Nothing -> do
             fatalTypeError p $ printf
               "in constructor, this does not have the field %s\n%s"
               n (show $ overrideFields fields fields')
    --special-case array literals:
    rhsTy <- case x of
      ArrayLit _ [] -> do
        moan <- projType isArrayType s
        case moan of
          Just (TApp "Array" [r]) -> return $ intersectType (TApp "Array" [r]) 
                      (openType r freeArrayType)
          Just _ -> catastrophe p "Terrible terrible not given array-ness"
          Nothing -> fatalTypeError p "assigning mt array lit to non-array fld"
      otherwise -> expr x
    r <- isSubtype rhsTy s
    case r of
      True -> constructorInit p rtt (S.delete n fieldsLeft) as
      False -> fatalTypeError p $ printf
        "Error assigning to field %s in constructor: field has type %s,\
         \ but given type %s" n (renderType s) (renderType rhsTy)
constructorInit p _ _ _ = fatalTypeError p "stop fooling around"

decl :: VarDecl SourcePos -> TypeCheck ()
decl (VarDecl p (Id _ x) t) = do
  t' <- desugarType p t
  r <- isSubtype undefType t'
  case r of
    True -> ok
    False -> fatalTypeError p "uninitalized variable declarations must \
                              \have type undefined"
decl (VarDeclExpr p (Id _ x) (Just t) (ArrayLit _ [])) = 
  -- empty array literal
  ok
decl (VarDeclExpr p (Id _ x) (Just t) e) = do
  s <- expr e
  t' <- desugarType p t
  r <- isSubtype s t'
  case r of
    True -> ok
    False -> do fatalTypeError p $ printf 
                  "expression has type\n%s\n, but was declared to have type\n%s"
                  (renderType s) (renderType t')
-- e may contain a function, therefore we must recompute the type.
decl (VarDeclExpr p (Id _ x) Nothing e) = do
  t <- lookupEnv p x
  s <- expr e
  case s == t of
    True -> ok
    False -> catastrophe p $ printf 
      "%s :: %s, but was calculated to have type %s"
      x (renderType s) (renderType t)
decl (UnpackDecl p (Id _ x) tVars e) = do
  t <- expr e
  let unpack ty tVar = case ty of
        TExists s -> return (openType (TId tVar) s)
        otherwise -> fatalTypeError p $ printf
          "RHS has type %s, but the type variables specified were %s"
          (renderType t) (show tVars)
  foldM unpack t tVars
  ok


topLevel :: TopLevel SourcePos -> TypeCheck ()
topLevel tl = case tl of
  ExternalFieldStmt p (Id _ brand) (Id _ field) e -> do
    tVars <- brandTVars p brand
    ty <- bindTVars tVars $ expr e
    extendBrand brand field ty
  ImportStmt p name isAssumed ty -> ok
  TopLevelStmt s -> stmt ToplevelInfo s
  c@(ConstructorStmt p brand args constrTy asgns body) -> do
    constrTy <- desugarType p constrTy
    newBrand brand (getConstrObj constrTy) (TObject "Object" [] [])
    -- TODO: newBrands need to be added at first. extensions added later
    -- for recursion, etc.
    
    --similar code to FuncExpr:
    let (qtVars, t') = unForall constrTy
    bindTVars qtVars $ do
      t <- desugarType p t'
      case t of
        TConstr cBrand argTypes initThisType --can be obj, or undefined
                                resultThisType@(TObject{}) -> do
          unless (length args == length (nub args)) $
            fatalTypeError p "function argument names must be unique"
          unless (length args == length argTypes) $
            fatalTypeError p "argument count mismatch"
          nestEnv $ extendsEnv (zip args argTypes) $ 
            extendEnv "this" resultThisType $ do
            rtEnv <- runtimeEnv
            localEnv <- declaredLocalTypes args body 
            body <- runtimeAnnotations rtEnv localEnv body
            (vars, tvars) <- localVars args body
            -- Calculating types affects the brand store.  Scope the 
            -- effects and recompute in the calculated environment.
            env <- tempBrandStore $ bindTVars tvars $ calcTypes vars $ ask
            let cinf = ConstructorInfo resultThisType
                         (objectFieldNames resultThisType)
            --make sure every field in resulting 'this' is initialized
            --but don't have 'this' bound yet
            
            unused <- constructorInit p resultThisType 
                        (objectFieldNames resultThisType) asgns            
            --type check the rest, keeping that in mind:
            local (const env) $ stmt cinf (constrBodyStmt p unused body)
            ok
        -- annotation on the constructor is not a constructor initThisTypee
        otherwise -> do
          fatalTypeError p $ printf "expected a constructor type, received %s" 
                               (renderType t)


--    stmt (ConstructorInfo constrTy S.empty) body
  ImportConstrStmt p (Id _ brand) isAssumed constrTy -> do
    constrTy <- desugarType p constrTy
    newBrand brand (getConstrObj constrTy) (TObject "Object" [] [])


-- |This code should be almost identical to the code for function bodies.
topLevelM :: [TopLevel SourcePos] -> TypeCheck ()
topLevelM body = do
  globals <- domEnv
  rtEnv <- runtimeEnv
  preTypeCheckTopLevel globals body
  case topLevelRuntimeAnnotations rtEnv body of
      -- body below is annotated with runtime type information
      Right body -> do
        (vars, tvars) <- topLevelVars globals body
        env <- tempBrandStore $ bindTVars tvars $ calcTypes vars $ ask
        local (const env) $ mapM_ topLevel body
      Left s -> catastrophe noPos s


withInitEnv m = do
  objTy <- brandType "Object" []
  newBrand "Array" (TForall freeArrayType) objTy
  newBrand "Number" numberObjectType objTy
  m


typeCheck :: InitialStoreEnv -> [TopLevel SourcePos] -> Either String ()
typeCheck init body = 
  case runTypeCheck init (withInitEnv $ topLevelM body) of
    Right () -> return ()
    Left errs -> Left errs


typeCheckExpr :: InitialStoreEnv -> Expression SourcePos -> Either String Type
typeCheckExpr init e = do
  [e] <- preTypeCheck (variablesInScope init) [ExprStmt noPos e]
  body <- runtimeAnnotations M.empty M.empty e
  case body of
    ExprStmt _ e -> case runTypeCheck init (withInitEnv $ expr e) of
      Right t -> return t
      Left errs -> Left errs
    otherwise -> fail "typeCheckExpr: expression shape error"
