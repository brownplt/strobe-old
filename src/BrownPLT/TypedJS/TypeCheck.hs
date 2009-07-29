module BrownPLT.TypedJS.TypeCheck
  ( typeCheck
  , typeCheckExpr
  , withInitEnv
  ) where

import BrownPLT.TypedJS.Infrastructure
import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.LocalVars
import BrownPLT.TypedJS.RuntimeAnnotations (runtimeAnnotations)
import BrownPLT.TypedJS.TypeDefinitions
import BrownPLT.TypedJS.TypeTheory
import BrownPLT.TypedJS.PrettyPrint
import BrownPLT.TypedJS.Syntax
import qualified Data.Map as M
import qualified Data.Set as S
import BrownPLT.TypedJS.PreTypeCheck
import Control.Monad.Reader
import Control.Monad.Error


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


ok :: TypeCheck ()
ok = return ()






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
    extendEnv x u m
  DeclExpr x (FuncExpr _ _ t _) -> do
    u <- desugarType noPos t
    extendEnv x u m
  DeclExpr x e -> do
    t <- expr e
    extendEnv x t m
  DeclField brand field (FuncExpr _ _ t _) ->  do
    t <- desugarType noPos t
    extendBrand brand field t
    m
  DeclField brand field e -> do
    t <- expr e
    extendBrand brand field t
    m

calcTypes :: [LocalDecl]
          -> TypeCheck a
          -> TypeCheck a
calcTypes binds m = foldr (flip calcType) m binds


field :: (Prop SourcePos,  Expression SourcePos)
      -> TypeCheck Field
field f = case f of
  (PropId p (Id _ x), e) -> do
    t <- expr e
    return (x, False, t) -- fields are mutable by default
         
 
numericOp :: SourcePos -> Expression SourcePos
          -> Type -> Type -> Bool -> Bool -> TypeCheck Type
numericOp loc e lhs rhs requireInts returnDouble = do
  result <- case returnDouble of
    True -> desugarType loc $ intersectType doubleType numberObjectType
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
      True -> fail "assinging to enclosing scopes NYI"
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
            fatalTypeError p $ printf "object %s\ndoes not have the field %s" 
                                      (renderType tObj) f
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
  NumLit p _ -> desugarType p $ intersectType doubleType numberObjectType
  IntLit p _ -> desugarType p $ intersectType intType numberObjectType
  BoolLit _ _ -> return boolType
  NullLit _ -> fail "NullLit NYI"
  ThisRef p -> lookupEnv p "this"
  ArrayLit p [] -> fatalTypeError p $ printf
    "empty array literals must be bound to identifiers with type annotations."
  ArrayLit p (e1:es) -> do
    t1 <- expr e1
    ts <- mapM expr es
    let t = foldr unionType t1 ts
    -- desugaring fills in the array methods
    desugarType p $ intersectType (TApp "Array" [t]) (openType t freeArrayType)
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
            "%s\ndoes not have the field %s" (renderType objTy) x
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
              "%s may only be applied to numbers and strings" (show op)
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
    let names = map fst fields
    -- Confirmed in Rhino that this is not a syntax error in JavaScript.
    unless (length fields == length (nub names)) $
      fatalTypeError p "duplicate field names"
    ts <- mapM field fields
    t <- desugarType p (TObject "Object" [] ts)
    s <- getBrand "Object"
    case (t, s) of
      (TObject "Object" [] fs1, TObject "Object" [] fs2) ->
        return (TObject "Object" [] (overrideFields fs1 fs2))
      otherwise -> 
        catastrophe p "TypeCheck.hs : desugarType/getBrand error in ObjectLit"
    
  CallExpr p f ts args -> do
    f_t <- expr f
    args_t <- mapM expr args
    case f_t of
      TArrow thisType (ArgType argTypes optArgType) resultType -> do
        unless (length args == length argTypes) $ 
          fatalTypeError p "argument count mismatch"
        argsMatch <- liftM and (mapM (uncurry isSubtype) (zip args_t argTypes))
        unless argsMatch $
          fatalTypeError p "argument type mismatch"
        return resultType
      otherwise -> do
        fatalTypeError p $ printf "expected a function; expression has type %s"
          (renderType f_t)
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
          nestEnv $ extendsEnv (zip (map unId args) argTypes) $ do
            rtEnv <- runtimeEnv
            case runtimeAnnotations rtEnv body of
              Left s -> catastrophe p s
              Right body -> case localVars (map unId args) body of
                Left err -> fatalTypeError p err -- duplicate name error
                Right (vars, tvars) -> do
                  -- Calculating types affects the brand store.  Scope the 
                  -- effects and recompute in the calculated environment.
                  env <- tempBrandStore $ bindTVars tvars $ calcTypes vars $ ask
                  local (const env) $ stmt (Just resultType) body
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
          Just t -> return t
          Nothing -> catastrophe p $ 
            printf "%s :: %s is inconsistent with the runtime type %s" 
                   x (renderType s) (show rt)
  PackExpr p e c t -> do
    t <- desugarType p t
    case t of
      TExists t' -> do
        s <- expr e
        isSt <- isSubtype s (openType c t')
        case isSt of
          True -> return (TExists t')
          False -> do
            fatalTypeError p $ printf "expected %s to have the shape %s"
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
        
  


stmt :: Maybe Type -- ^ return type
     -> Statement SourcePos
     -> TypeCheck ()
stmt returnType s = case s of
  BlockStmt _ ss -> mapM_ (stmt returnType) ss
  EmptyStmt _ -> ok
  ExprStmt _ e -> expr e >> ok
  IfStmt _ e s1 s2 -> do
    expr e -- we permit non-boolean tests
    stmt returnType s1
    stmt returnType s2
  IfSingleStmt _ e s -> do
    expr e -- we permit non-boolean tests
    stmt returnType s
  SwitchStmt _ e cases -> do
    expr e
    let case_ (CaseClause _ e ss) = do
          expr e
          mapM_ (stmt returnType) ss
        case_ (CaseDefault _ ss) =
          mapM_ (stmt returnType) ss
    mapM_ case_ cases
  WhileStmt _ e s -> do
    expr e
    stmt returnType s
  DoWhileStmt _ s e -> do
    stmt returnType s
    expr e
    ok
  BreakStmt _ _ -> ok
  ContinueStmt _ _ -> ok
  LabelledStmt _ _ s -> stmt returnType s
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
    stmt returnType s
  TryStmt _ body catches finally -> fail "TryStmt NYI"
  ThrowStmt _ e -> expr e >> ok
  ReturnStmt p ret -> case returnType of
    Nothing -> fatalTypeError p $ printf 
      "return used in a constructor or at the top level"
    Just returnType -> case ret of
      Nothing -> do
        r <- isSubtype undefType returnType
        case r of
          True -> ok
          False -> fatalTypeError p $ printf 
                     "empty return, expected %s" 
                     (renderType returnType)
      Just e -> do
        t <- expr e
        r <- isSubtype t returnType
        case r of
          True -> ok
          False -> fatalTypeError p $ printf 
            "statement returns\n%s\nExpected\n%s"
                     (renderType t) (renderType returnType)
  VarDeclStmt p decls -> mapM_ (decl) decls
  ExternalFieldStmt p (Id _ brand) (Id _ field) e -> do
    ty <- expr e
    extendBrand brand field ty
    

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
decl (UnpackDecl p (Id _ x) tVar t e) = do
  t <- desugarType p t
  s <- expr e
  case s of
    TExists s' -> do
      r <- isSubtype (openType (TId tVar) s') t
      case r of
        True -> ok
        False -> fatalTypeError p $ printf
          "expression has type %s, bound to an identifier of type %s"
          (renderType (openType (TId x) s')) (renderType t)
    otherwise -> fatalTypeError p $ printf
      "unpack used on an expression of type %s" (renderType s)


-- |This code should be almost identical to the code for function bodies.
topLevel :: [Statement SourcePos] -> TypeCheck ()
topLevel body = do
  globals <- domEnv
  rtEnv <- runtimeEnv
  case preTypeCheck globals body of
    Right e -> case runtimeAnnotations rtEnv (BlockStmt noPos e) of
      Right body -> case localVars globals body of
        Right (vars, tvars) -> do
          env <- tempBrandStore $ bindTVars tvars $ calcTypes vars $ ask
          local (const env) $ stmt Nothing body
        Left err -> fatalTypeError noPos err
      Left s -> catastrophe noPos s
    Left str -> fatalTypeError noPos str


withInitEnv m = do
  newBrand "Array" (TForall freeArrayType) (TObject "Object" [] [])
  newBrand "Number" numberObjectType (TObject "Object" [] [])
  m


typeCheck :: InitialStoreEnv -> [Statement SourcePos] -> Either String ()
typeCheck init body = 
  case runTypeCheck init (withInitEnv $ topLevel body) of
    Right () -> return ()
    Left errs -> Left errs


typeCheckExpr :: InitialStoreEnv -> Expression SourcePos -> Either String Type
typeCheckExpr init e = do
  [e] <- preTypeCheck (variablesInScope init) [ExprStmt noPos e]
  body <- runtimeAnnotations M.empty e
  case body of
    ExprStmt _ e -> case runTypeCheck init (withInitEnv $ expr e) of
      Right t -> return t
      Left errs -> Left errs
    otherwise -> fail "typeCheckExpr: expression shape error"
