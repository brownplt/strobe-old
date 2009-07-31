module BrownPLT.TypedJS.TypeTheory
  ( undefType
  , stringType
  , intType
  , doubleType
  , boolType
  , freeArrayType
  , numberObjectType
  -- * Substitution
  --
  -- | We use a locally nameless representation for quantified types.  These
  -- are the various kinds of substitution available.
  , substType
  , openType
  , closeType
  , (+++)
  , (-=-)
  , isWfType
  , canonicalUnion 
  , intersectType
  , unionType
  -- * Subtyping
  , isSubtype
  , areSubtypes
  , projFieldType
  , projType
  , projBrand
  -- * Interface to dataflow analysis
  -- $runtime
	, static
	, runtime
  -- * Utilities
  , desugarType
  , canonize
  , lcType
  , fieldType
  , overrideFields
  , intersectBrand
  , brandType
  , unForall
  ) where

import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.TypeDefinitions
import qualified Data.Set as S
import BrownPLT.TypedJS.Infrastructure
import BrownPLT.TypedJS.PrettyPrint (renderType)
import Control.Monad.Error


undefType = TApp "Undefined" []

stringType = TApp "String" []

intType = TApp "Int" []

doubleType = TApp "Double" []

boolType = TApp "Bool" []


freeArrayType = TObject "Array" [TIx 0]
  [ ("length", True, intersectType intType numberObjectType)
  , ("push", True, TArrow (TApp "Array" [TIx 0]) (ArgType [TIx 0] Nothing)
                          undefType)
  ]

-- |Note that field names must be in ascending order.
numberObjectType = TObject "Number" []
  [ ("toExponential", True,
     TArrow (TObject "Number" [] []) 
            (ArgType [unionType intType undefType] Nothing)
            stringType)
  , ("toFixed", True,
     TArrow (TObject "Number" [] []) 
            (ArgType [unionType intType undefType] Nothing)
            stringType)
  , ("toLocaleString", True,
     TArrow (TObject "Number" [] []) 
            (ArgType [] Nothing)
            stringType)
  , ("toPrecision", True,
     TArrow (TObject "Number" [] []) 
            (ArgType [unionType intType undefType] Nothing)
            stringType)
  , ("valueOf", True,
     TArrow (TObject "Number" [] []) 
            (ArgType [] Nothing)
            doubleType)
  ]


closeTypeRec :: Int -> String -> Type -> Type
closeTypeRec n x t = case t of
  TObject brand args fields ->
    TObject brand (map (closeTypeRec n x) args) (map f fields)
      where f (lbl, imm, t') = (lbl, imm, closeTypeRec n x t')
  TAny -> TAny
  TArguments arg -> TArguments (closeArgTypeRec n x arg)
  TArrow this arg ret ->
    TArrow (closeTypeRec n x this) 
           (closeArgTypeRec n x arg) 
           (closeTypeRec n x ret)
  TId y | x == y -> TIx n
        | otherwise -> TId y
  TIx m -> TIx m
  TApp constr ts ->
    TApp constr (map (closeTypeRec n x) ts)
  TUnion t1 t2 ->
    TUnion (closeTypeRec n x t1) (closeTypeRec n x t2)
  TExists u -> TExists (closeTypeRec (n + 1) x u)
  TForall u -> TForall (closeTypeRec (n + 1) x u)
  TNamedForall y u 
    | y == x -> t
    | otherwise -> TNamedForall y (closeTypeRec (n + 1) x u)
  TIntersect t1 t2 ->
    TIntersect (closeTypeRec n x t1) (closeTypeRec n x t2)
  TConstr argTys initTy objTy -> 
    TConstr (map (closeTypeRec n x) argTys) 
            (closeTypeRec n x initTy)
            (closeTypeRec n x objTy)


closeArgTypeRec n x (ArgType ts opt) =
  ArgType (map (closeTypeRec n x) ts) 
          (liftM (closeTypeRec n x) opt)


closeType :: String -> Type -> Type
closeType x t = closeTypeRec 0 x t


-- |'openTypeRec n s t' replaces the bound type variable 'n' in 't' with the 
-- locally closed type 's'.
openTypeRec :: Int -> Type -> Type -> Type
openTypeRec n s t = case t of
  TObject brand args fields ->
    TObject brand (map (openTypeRec n s) args) (map f fields)
      where f (lbl, imm, t') = (lbl, imm, openTypeRec n s t')
  TAny -> TAny
  TArguments arg -> TArguments (openArgTypeRec n s arg)
  TArrow this arg ret ->
    TArrow (openTypeRec n s this) (openArgTypeRec n s arg) (openTypeRec n s ret)
  TIx m
    | m == n -> s
    | otherwise -> TIx m
  TId x -> TId x
  TApp constr ts ->
    TApp constr (map (openTypeRec n s) ts)
  TUnion t1 t2 ->
    TUnion (openTypeRec n s t1) (openTypeRec n s t2)
  TIntersect t1 t2 ->
    TIntersect (openTypeRec n s t1) (openTypeRec n s t2)
  TExists u -> TExists (openTypeRec (n + 1) s u)
  TForall u -> TForall (openTypeRec (n + 1) s u)
  TConstr argTys initTy objTy -> 
    TConstr (map (openTypeRec n s) argTys)
            (openTypeRec n s initTy)
            (openTypeRec n s objTy)


openArgTypeRec n s (ArgType ts opt) =
  ArgType (map (openTypeRec n s) ts) (liftM (openTypeRec n s) opt)


-- |'openType s t' replaces bound variables in 't' with the locally closed 
-- type  's'.
openType :: Type -> Type -> Type
openType s t = openTypeRec 0 s t
  

-- |'substTId x s t' substitutes free type variables 'x' with the locally closed
-- type 's', in the locally closed type 't'.
substType :: String -> Type -> Type -> Type
substType x s t = case t of
  TObject brand args fields ->
    TObject brand (map (substType x s) args) (map f fields)
      where f (lbl, imm, t') = (lbl, imm, substType x s t')
  TAny -> TAny
  TArguments arg -> TArguments (substTypeInArgType x s arg)
  TArrow this arg ret ->
    TArrow (substType x s this) (substTypeInArgType x s arg) (substType x s ret)
  TId y | x == y -> s
        | otherwise -> TId y
  TIx n -> TIx n
  TApp constr ts ->
    TApp constr (map (substType x s) ts)
  TUnion t1 t2 ->
    TUnion (substType x s t1) (substType x s t2)
  TIntersect t1 t2 ->
    TIntersect (substType x s t1) (substType x s t2)
  TExists u -> TExists (substType x s u)
  TForall u -> TForall (substType x s u)


substTypeInArgType x s (ArgType ts opt) =
  ArgType (map (substType x s) ts) (liftM (substType x s) opt)


(+++) :: Monad m => m Bool -> m Bool -> m Bool
m1 +++ m2 = do
  r1 <- m1
  case r1 of
    True -> m2
    False -> return False

(-=-) :: Monad m => m Bool -> m Bool -> m Bool
m1 -=- m2 = do
  r1 <- m1
  case r1 of
    True -> return True
    False -> m2



canonizeArgType :: EnvM m => ArgType -> m ArgType
canonizeArgType (ArgType args Nothing) = do
  args <- mapM canonize args
  return (ArgType args Nothing)
canonizeArgType (ArgType args (Just opt)) = do
  args <- mapM canonize args
  opt <- canonize opt
  return (ArgType args (Just opt))


lcArgType (ArgType args Nothing) = ArgType (map lcType args) Nothing
lcArgType (ArgType args (Just opt)) =
  ArgType (map lcType args) (Just $ lcType opt)


lcType :: Type -> Type
lcType ty = case ty of
  TAny -> TAny
  TApp c args -> TApp c (map lcType args)
  TArguments at -> TArguments (lcArgType at)
  TArrow this arg r ->TArrow (lcType this) (lcArgType arg) (lcType r)
  TUnion t1 t2 -> TUnion (lcType t1) (lcType t2)
  TIntersect t1 t2 -> TIntersect (lcType t1) (lcType t2)
  TObject brand tyArgs fields ->
    TObject brand (map lcType tyArgs) (map lcField fields)
    where lcField (x, ro, t) = (x, ro, lcType t)
  TId x -> TId x
  TIx x -> TIx x
  TExists u -> TExists (lcType u)
  TForall u -> TForall (lcType u)
  TConstr argTys initTy objTy -> 
    TConstr (map lcType argTys) (lcType initTy) (lcType objTy)
  TNamedForall x u -> TForall (lcType (closeType x u))


-- |Canonizes types such as int U int to int.  Orders fields lexicographically.
canonize:: EnvM m => Type -> m Type
canonize t = case t of
  TAny -> return t
  TApp c args -> liftM (TApp c) (mapM canonize args)
  TArguments at -> 
    liftM TArguments (canonizeArgType at)
  TArrow this arg r ->
    liftM3 TArrow (canonize this) (canonizeArgType arg) (canonize r)
  TUnion t1 t2 ->
    liftM2 unionType (canonize t1) (canonize t2)
  TIntersect t1 t2 ->
    liftM2 intersectType (canonize t1) (canonize t2)
  TObject brand tyArgs fields -> do
    let cmp (x, _, _) (y, _, _) = compare x y
    let fields' = sortBy cmp fields
    let f (x, ro, t) = do
          t' <- canonize t
          return (x, ro, t')
    fields'' <- mapM f fields'
    tyArgs' <- mapM canonize tyArgs
    return (TObject brand tyArgs' fields'')
  TId x -> return (TId x)
  TIx x -> return (TIx x)
  TExists u -> liftM TExists (canonize u)
  TForall u -> liftM TForall (canonize u)
  TConstr argTys initTy objTy -> 
    liftM3 TConstr (mapM canonize argTys) (canonize initTy) (canonize objTy)
  TNamedForall x u -> liftM (TNamedForall x) (canonize u)


-- |Assumes that the components are already canonized.
canonicalUnion :: EnvM m => Type -> Type -> m Type
canonicalUnion t1 t2
  | t1 == t2  = return t1
  | t1 < t2   = return (TUnion t1 t2)
  | otherwise = return (TUnion t2 t1)


unionType t1 t2
  | t1 == t2  = t1
  | t1 < t2   = (TUnion t1 t2)
  | otherwise = (TUnion t2 t1)


intersectType t1 t2
  | t1 == t2  = t1
  | t1 < t2   = (TIntersect t1 t2)
  | otherwise = (TIntersect t2 t1)



isWfType :: EnvM m
         => Type
         -> ErrorT String m ()
isWfType ty = case ty of
  TAny -> return ()
  TApp c args -> mapM_ isWfType args
  TArguments at ->  isWfArgType at
  TArrow this arg r -> do
    isWfType this
    isWfArgType arg
    isWfType r
  TUnion t1 t2 -> do
    isWfType t1
    isWfType t2
  TIntersect t1 t2 -> do
    isWfType t1
    isWfType t2
  TObject brand tys fields -> do
    mapM_ isWfType tys >> mapM_ isWfField fields
      where isWfField (x, ro, t) = isWfType t
{-
    r <- isBrand brand 
    case r of
      True -> mapM_ isWfType tys >> mapM_ isWfField fields
        where isWfField (x, ro, t) = isWfType t
      False -> fail $ printf "the brand %s is undefined" brand
-}
  TId x -> do
    tv <- lookupTVar x
    case tv of
      Just BoundTVar -> return ()
      Nothing -> fail $ printf "the type variable %s is unbound" x
  TIx x -> fail "the type is not locally closed"
  TExists u -> freshTVar $ \x -> bindTVar x $ isWfType (openType (TId x) u)
  TForall u -> freshTVar $ \x -> bindTVar x $ isWfType (openType (TId x) u)
  TConstr tyArgs initTy constrTy -> do
    --TODO: Check that initTy is well-formed
    mapM_ isWfType tyArgs
    isWfType constrTy
  TNamedForall x u -> bindTVar x $ isWfType u


isWfArgType :: EnvM m => ArgType -> ErrorT String m ()
isWfArgType (ArgType args Nothing) = mapM_ isWfType args
isWfArgType (ArgType args (Just opt)) = do
  mapM_ isWfType args
  isWfType opt


-- ----------------------------------------------------------------------------
-- Subtyping

areSubtypes :: EnvM m
            => [Type]
            -> [Type]
            -> m Bool
areSubtypes [] [] = return True
areSubtypes (s:ss) (t:ts) = isSubtype s t +++ areSubtypes ss ts
areSubtypes _ _ = return False


-- Width and subsumption.  'canonize' handles permutations.
areFieldsSubtypes :: EnvM m
                  => [Field] -> [Field] -> m Bool
areFieldsSubtypes _ [] = return True
areFieldsSubtypes [] _ = return False
areFieldsSubtypes ((x1, ro1, t1):fs1) ((x2, ro2, t2):fs2)
  | x1 < x2 = areFieldsSubtypes fs1 ((x2, ro2, t2):fs2)
  | x1 == x2 = case (ro1, ro2) of
      (True, False) -> return False
      (False, False) -> 
        isSubtype t1 t2 +++ isSubtype t2 t1 +++ areFieldsSubtypes fs1 fs2
      (_, True) -> isSubtype t1 t2 +++ areFieldsSubtypes fs1 fs2
  | otherwise = return False


-- |Assumes the arguments are canonical.
isSubtype :: EnvM m
          => Type
          -> Type
          -> m Bool
isSubtype s t = case (s, t) of
  (TIx _, _) -> fail "TypeTheory.hs : LHS of iSubtype is not locally closed"
  (_, TIx _) -> fail "TypeTheory.hs : RHS of iSubtype is not locally closed"
  (_, TAny) ->
    return True
  (TApp "Int" [], TApp "Double" []) ->
    return True
  (TApp "Array" [s1], TApp "Array" [t1]) ->
    isSubtype s1 t1 +++ isSubtype t1 s1
  (TObject brand1 tys1 fs1, TObject brand2 tys2 fs2) -> do
    let intersectSubtype = do
          fs1' <- intersectBrand brand1 tys1
          fs2' <- intersectBrand brand2 tys2
          areFieldsSubtypes (overrideFields fs1 fs1') (overrideFields fs2 fs2')
    isSubbrand brand1 brand2 +++
      areSubtypes tys1 tys2 +++
      (areFieldsSubtypes fs1 fs2 -=- intersectSubtype)
  (TApp c1 args1, TApp c2 args2) -> case c1 == c2 of
    True -> areSubtypes args1 args2
    False -> return False
  (TArguments (ArgType args1 optArg1), TArguments (ArgType args2 optArg2)) ->
    areSubtypes args1 args2 -- TODO: arity, blah blah blah
  (TArrow this1 args1 r1, TArrow this2 args2 r2) ->
    -- isSubtype this2 this1 +++
    isSubtype (TArguments args2) (TArguments args1) +++
    isSubtype r1 r2
  (TUnion s1 s2, _) -> 
    isSubtype s1 t +++ isSubtype s2 t
  (_, TUnion t1 t2) -> do
    r <- isSubtype s t1
    case r of
      True -> return True
      False -> isSubtype s t2
  (TId x, TId y) -> return (x == y)
  (TExists t1, TExists t2) -> freshTVar $ \x ->
    bindTVar x $ isSubtype (openType (TId x) t1) (openType (TId x) t2)
  (TForall t1, TForall t2) -> freshTVar $ \x ->
    bindTVar x $ isSubtype (openType (TId x) t1) (openType (TId x) t2)
  (TNamedForall x s', _) ->
    isSubtype (TForall (closeType x s')) t
  (_, TNamedForall x t') ->
    isSubtype s (TForall (closeType x t'))
  (_, TIntersect t1 t2) ->
    liftM2 (&&) (isSubtype s t1) (isSubtype s t2)
  (TIntersect s1 s2, _) ->
    liftM2 (||) (isSubtype s1 t) (isSubtype s2 t)
  otherwise -> return False


projBrand :: EnvM m => Type -> m (Maybe (String, [Type]))
projBrand ty = case ty of
  TObject brand tyArgs fields -> return (Just (brand, tyArgs))
  TIntersect t1 t2 -> do
    r1 <- projBrand t1
    r2 <- projBrand t2
    case (r1, r2) of
      (Just (brand1, tyArgs1), Just (brand2, tyArgs2)) -> do
        sb1 <- isSubbrand brand1 brand2 +++ areSubtypes tyArgs1 tyArgs2
        sb2 <- isSubbrand brand2 brand1 +++ areSubtypes tyArgs2 tyArgs1
        case (sb1, sb2) of
          (True, _) -> return (Just (brand1, tyArgs1))
          (_, True) -> return (Just (brand2, tyArgs2))
          (False, False) -> error $ printf 
            "projBrand: intersection of unrelated brands %s and %s"
            brand1 brand2
      (Just brand1, Nothing) -> return (Just brand1)
      (Nothing, Just brand2) -> return (Just brand2)
      (Nothing, Nothing) -> return Nothing
  TUnion t1 t2 -> do
    r1 <- projBrand t1
    r2 <- projBrand t2
    case (r1, r2) of
      (Just (brand1, tyArgs1), Just (brand2, tyArgs2)) ->  do
        isEq <- (return $ brand1 == brand2) +++ 
                areSubtypes tyArgs1 tyArgs2 +++ 
                areSubtypes tyArgs2 tyArgs1
        return $ if isEq then Just (brand1, tyArgs1) else Nothing
      otherwise -> return Nothing
  otherwise -> return Nothing


projFieldType :: EnvM m => Type -> String -> m (Maybe Type)
projFieldType ty name = case ty of
  TObject brand tyArgs fields -> do
--   fields' <- intersectBrand brand tyArgs
   case fieldType name fields of -- (overrideFields fields fields') of
     Just (ty, _) -> return (Just ty)
     Nothing -> return Nothing
  TIntersect t1 t2 -> do
    r1 <- projFieldType t1 name
    r2 <- projFieldType t2 name
    case (r1, r2) of
      (Just ty1, Nothing) -> return (Just ty1)
      (Nothing, Just ty2) -> return (Just ty2)
      (Just ty1, Just ty2) -> return (Just (intersectType ty1 ty2))
      (Nothing, Nothing) -> return Nothing
  TUnion t1 t2 -> do
    r1 <- projFieldType t1 name
    r2 <- projFieldType t2 name
    case (r1, r2) of
      (Just ty1, Just ty2) -> return (Just (unionType ty1 ty2))
      otherwise -> return Nothing
  otherwise -> return Nothing


projType :: EnvM m => (Type -> Bool) -> Type -> m (Maybe Type)
projType isType ty = case ty of
  TObject brand tyArgs fields -> do
   fields' <- intersectBrand brand tyArgs
   let ty' = TObject brand tyArgs (overrideFields fields fields')
   case isType ty' of
     True -> return (Just ty')
     False -> return Nothing
  TIntersect t1 t2 -> do
    r1 <- projType isType t1
    r2 <- projType isType t2
    case (r1, r2) of
      (Just ty1, Nothing) -> return (Just ty1)
      (Nothing, Just ty2) -> return (Just ty2)
      (Just ty1, Just ty2) -> return (Just (intersectType ty1 ty2))
      (Nothing, Nothing) -> return Nothing
  TUnion t1 t2 -> do
    r1 <- projType isType t1
    r2 <- projType isType t2
    case (r1, r2) of
      (Just ty1, Just ty2) -> return (Just (unionType ty1 ty2))
      otherwise -> return Nothing
  otherwise -> case isType ty of
    True -> return (Just ty)
    False -> return Nothing


-- ----------------------------------------------------------------------------
-- $runtime
-- Interface between the type system and the dataflow analysis


injRT :: RuntimeType -> RuntimeTypeInfo
injRT bt = TKnown (S.singleton bt)


runtime :: Type -> RuntimeTypeInfo
runtime t = case t of
  TId x -> TUnk
  TIx _ -> TUnk
  TExists t -> runtime t
  TForall t -> runtime t
  TNamedForall _ t -> runtime t
  TConstr _ _ _ -> injRT RTFunction
  TAny -> TUnk
  TApp "String" [] ->  injRT RTString
  TApp "Bool" [] ->  injRT RTBoolean
  TApp "Double" [] ->  injRT RTNumber
  TApp "Int" [] ->  injRT RTNumber
  TApp "Undefined" [] ->  injRT RTUndefined
  TApp "Array" [_] -> injRT RTObject
  TApp x ts -> error $ printf "TypeTheory.hs : argument of runtime contains \
                              \unknown type constructor %s, with args %s"
                              x (show ts) 
  TObject "Number" _ _ -> injRT RTNumber
  TObject _ _ _ -> injRT RTObject
  TArguments _ -> injRT RTObject -- the type of the arguments array
  TArrow _ _ _ -> injRT RTFunction
  TIntersect t1 t2 -> case (runtime t1, runtime t2) of
    (TUnk, TKnown s2) -> TKnown s2
    (TKnown s1, TUnk) -> TKnown s1
    (TKnown s1, TKnown s2) -> TKnown (S.intersection s1 s2)
    (TUnk, TUnk) -> TUnk
    (TUnreachable, _) -> error "runtime: recursive call produced TUnreachable"
    (_, TUnreachable) -> error "runtime: recursive call produced TUnreachable"
  TUnion t1 t2 -> case (runtime t1, runtime t2) of
    (TUnk, _) -> TUnk
    (_, TUnk) -> TUnk
    -- cases above should not happen if t is canonized
    (TKnown s1, TKnown s2) -> TKnown (S.union s1 s2)
    (TUnreachable, _) -> error "runtime: recursive call produced TUnreachable"
    (_, TUnreachable) -> error "runtime: recursive call produced TUnreachable"


flatStatic :: EnvM m => RuntimeType -> m Type
flatStatic rt = case rt of
  RTBoolean -> return boolType
  RTNumber -> desugarType noPos $ intersectType doubleType numberObjectType
  RTUndefined -> return undefType
  RTString -> return stringType
  RTObject -> return TAny
  RTFunction -> return TAny
  RTFixedString _ -> return stringType


-- |If the supplied type is canonical, the result is canonical.
static :: EnvM m
       => Set RuntimeType 
       -> Type 
       -> m (Maybe Type)
static rt st = case st of
  TId x | not (S.null rt) -> return (Just st)
  TIx _ | not (S.null rt) -> return (Just st)
  TExists t -> do
    r <- static rt t
    case r of
      Just t' -> return (Just $ TExists t')
      Nothing -> return Nothing
  TForall t -> do
    r <- static rt t
    case r of
      Just t' -> return (Just $ TForall t')
      Nothing -> return Nothing
  TNamedForall x t -> do
    r <- static rt t
    case r of
      Just t' -> return (Just $ TNamedForall x t')
      Nothing -> return Nothing
  TAny -> do
    ts <- mapM flatStatic (S.toList rt)
    case ts of
      [] -> return Nothing
      [t] -> return (Just t)
      (t:ts) -> liftM Just (foldM canonicalUnion t ts)
  TApp "String" [] | S.member RTString rt -> return (Just st)
  TApp "Bool" [] | S.member RTBoolean rt -> return (Just st)
  TApp "Double" [] | S.member RTNumber rt -> return (Just st)
  TApp "Int" [] | S.member RTNumber rt -> return (Just st)
  TApp "Undefined" [] | S.member RTUndefined rt -> return (Just st)
  TApp "Array" [_] | S.member RTObject rt -> return (Just st)
  TObject "Number" _ _ | S.member RTNumber rt -> return (Just st)
  TObject _ _ _ | S.member RTObject rt -> return (Just st)
  TArrow _ _ _ | S.member RTFunction rt -> return (Just st)
  TUnion t1 t2 -> do
    r1 <- static rt t1
    r2 <- static rt t2
    case (r1, r2) of
      (Just u1, Just u2) -> return (Just $ unionType u1 u2)
      (Just u1, Nothing) -> return (Just u1)
      (Nothing, Just u2) -> return (Just u2)
      (Nothing, Nothing) -> return Nothing
  TIntersect t1 t2 -> do
    r1 <- static rt t1
    r2 <- static rt t2
    case (r1, r2) of
      (Just u1, Just u2) -> return (Just $ intersectType u1 u2)
      otherwise -> return Nothing
  otherwise -> return Nothing


-- ----------------------------------------------------------------------------
-- Utilities


desugarType :: EnvM m => SourcePos -> Type -> m Type
desugarType p ty = do
  r <- runErrorT (isWfType ty)
  case r of
    Right () ->  canonize ty
    Left msg -> fatalTypeError p $ printf "%s in type %s" msg (renderType ty)


fieldType :: String
          -> [Field]
          -> Maybe (Type, Bool) -- ^flag is true if it is immutable
fieldType name [] = Nothing
fieldType name ((name', ro, ty):rest)
  | name == name' = Just (ty, ro)
  | name' > name = Nothing
  | otherwise = fieldType name rest


overrideFields :: [Field] -> [Field] -> [Field]
overrideFields [] ys = ys
overrideFields xs [] = xs
overrideFields xs@((n1, ro1, ty1):xs') ys@((n2, ro2, ty2):ys')
  | n1 < n2 = (n1, ro1, ty1):(overrideFields xs' ys)
  | n1 == n2 = (n1, ro1, ty1):(overrideFields xs' ys')
  | otherwise = (n2, ro2, ty2):(overrideFields xs ys')


-- |@getBrandPath brand@
-- 
-- Returns the type of @brand@ and all its ancestors in order.  @brand@ is at
-- the head of the list.
getBrandPath :: EnvM m
             => String -- ^brand
             -> m [Type]
getBrandPath brand = do
  (ty, parent) <- getBrandWithParent brand
  case parent of
    Nothing -> return [ty]
    Just (TObject parentBrand _ _) -> do
      tys <- getBrandPath parentBrand
      return (ty:tys)
    Just _ -> error "getBrandPath: inconsistent brand store"

tyApp :: Type -> [Type] -> Type
tyApp t [] = t
tyApp (TForall t) (s:ss) = tyApp (openType s t) ss
tyApp (TNamedForall x t) (s:ss) = tyApp (substType x s t) ss
tyApp _ _ = error "tyApp: superflous type arguments"


brandType :: EnvM m
            => String
            -> [Type]
            -> m Type
brandType brand tyArgs = do
  fields <- intersectBrand brand tyArgs
  return (TObject brand tyArgs fields)


-- TODO: This is guesswork.
intersectBrand :: EnvM m
               => String
               -> [Type]
               -> m [Field]
intersectBrand brand tyArgs = do
  (ty', parentTy) <- getBrandWithParent brand
  let ty = tyApp ty' tyArgs
  case (ty, parentTy) of
    (TObject _ _ fields, Just (TObject parentBrand _ _)) -> do
      tys <- getBrandPath parentBrand
      let f (TObject _ _ fs) = fs
          f t = error $ printf
                  "intersectBrand: expected TObject in brand path, got %s"
                  (renderType t)
      return (foldr overrideFields fields (map f tys))
    (TObject _ _ fields, Nothing) -> return fields
    otherwise -> error "intersectBrand: need more args"


unForall :: Type -> ([String], Type)
unForall (TNamedForall x t) = (x:xs, s)
  where (xs, s) = unForall t
unForall t = ([], t)
