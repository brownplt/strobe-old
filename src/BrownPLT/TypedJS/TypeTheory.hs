module BrownPLT.TypedJS.TypeTheory
  ( undefType
  , stringType
  , intType
  , doubleType
  , boolType
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
  , canonize
  , canonicalUnion 
  -- * Subtyping
  , isSubtype
  -- * Interface to dataflow analysis
  -- $runtime
	, static
	, runtime
  -- * Utilities
  , fieldType
  , overrideFields
  , intersectBrand
  , brandSugar
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


closeTypeRec :: Int -> String -> Type -> Type
closeTypeRec n x t = case t of
  TObject brand fields -> TObject brand (map f fields)
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


closeArgTypeRec n x (ArgType ts opt) =
  ArgType (map (closeTypeRec n x) ts) 
          (liftM (closeTypeRec n x) opt)


closeType :: String -> Type -> Type
closeType x t = closeTypeRec 0 x t


-- |'openTypeRec n s t' replaces the bound type variable 'n' in 't' with the 
-- locally closed type 's'.
openTypeRec :: Int -> Type -> Type -> Type
openTypeRec n s t = case t of
  TObject brand fields -> TObject brand (map f fields)
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
  TExists u -> TExists (openTypeRec (n + 1) s u)
  TForall u -> TForall (openTypeRec (n + 1) s u)


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
  TObject brand fields -> TObject brand (map f fields)
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


-- |Canonizes types such as int U int to int.  Orders fields lexicographically.
canonize:: EnvM m => Type -> m Type
canonize t = case t of
  TAny -> return t
  TApp c args -> liftM (TApp c) (mapM canonize args)
  TArguments at -> 
    liftM TArguments (canonizeArgType at)
  TArrow this arg r ->
    liftM3 TArrow (canonize this) (canonizeArgType arg) (canonize r)
  TUnion t1 t2 -> do
    u1 <- canonize t1
    u2 <- canonize t2
    canonicalUnion u1 u2
  TObject brand fields -> do
    let cmp (x, _, _) (y, _, _) = compare x y
    let fields' = sortBy cmp fields
    let f (x, ro, t) = do
          t' <- canonize t
          return (x, ro, t')
    fields'' <- mapM f fields'
    return (TObject brand fields'')
  TId x -> return (TId x)
  TIx x -> return (TIx x)
  TExists u -> liftM TExists (canonize u)
  TForall u -> liftM TForall (canonize u)
  TNamedForall x u -> liftM TForall (canonize (closeType x u))


-- |Assumes that the components are already canonized.
canonicalUnion :: EnvM m => Type -> Type -> m Type
canonicalUnion t1 t2
  | t1 == t2  = return t1
  | t1 < t2   = return (TUnion t1 t2)
  | otherwise = return (TUnion t2 t1)




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
  TObject brand fields -> do
    r <- isBrand brand 
    case r of
      True -> mapM_ isWfField fields
        where isWfField (x, ro, t) = isWfType t
      False -> fail $ printf "the brand %s is undefined" brand
  TId x -> do
    tv <- lookupTVar x
    case tv of
      Just BoundTVar -> return ()
      Nothing -> fail $ printf "the type variable %s is unbound" x
  TIx x -> fail "the type is not locally closed"
  TExists u -> freshTVar $ \x -> bindTVar x $ isWfType (openType (TId x) u)
  TForall u -> freshTVar $ \x -> bindTVar x $ isWfType (openType (TId x) u)
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
  (TObject brand1 [], TObject brand2 []) -> isSubbrand brand1 brand2
  (TObject brand1 fs1, TObject brand2 fs2) -> do
    sub <- isSubbrand brand1 brand2
    case sub of
      True -> do
        fs1' <- liftM (overrideFields fs1) (intersectBrand brand1)
        fs2' <- liftM (overrideFields fs2) (intersectBrand brand2)
        areFieldsSubtypes fs1' fs2' 
      False -> return False
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
  -- From "Intersection Types and Computational Effects" p.3.
  (_, TIntersect t1 t2) ->
    liftM2 (&&) (isSubtype s t1) (isSubtype s t2)
  (TIntersect s1 s2, _) ->
    liftM2 (||) (isSubtype s1 t) (isSubtype s2 t)
  otherwise -> 
    return False


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
  TObject _ _ -> injRT RTObject
  TArguments _ -> injRT RTObject -- the type of the arguments array
  TArrow _ _ _ -> injRT RTFunction
  TUnion t1 t2 -> case (runtime t1, runtime t2) of
    (TUnk, _) -> TUnk
    (_, TUnk) -> TUnk
    -- cases above should not happen if t is canonized
    (TKnown s1, TKnown s2) -> TKnown (S.union s1 s2)
    (TUnreachable, _) -> error "runtime: recursive call produced TUnreachable"
    (_, TUnreachable) -> error "runtime: recursive call produced TUnreachable"


flatStatic :: RuntimeType -> Type
flatStatic rt = case rt of
  RTBoolean -> boolType
  RTNumber -> doubleType
  RTUndefined -> undefType
  RTString -> stringType
  RTObject -> TAny
  RTFunction -> TAny
  RTFixedString _ -> stringType


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
  TAny -> case map flatStatic (S.toList rt) of
    [] -> return Nothing
    [t] -> return (Just t)
    (t:ts) -> liftM Just (foldM canonicalUnion t ts)
  TApp "String" [] | S.member RTString rt -> return (Just st)
  TApp "Bool" [] | S.member RTBoolean rt -> return (Just st)
  TApp "Double" [] | S.member RTNumber rt -> return (Just st)
  TApp "Int" [] | S.member RTNumber rt -> return (Just st)
  TApp "Undefined" [] | S.member RTUndefined rt -> return (Just st)
  TApp "Array" [_] | S.member RTObject rt -> return (Just st)
  TObject _ _ | S.member RTObject rt -> return (Just st)
  TArrow _ _ _ | S.member RTFunction rt -> return (Just st)
  TUnion t1 t2 -> do
    r1 <- static rt t1
    r2 <- static rt t2
    case (r1, r2) of
      (Just u1, Just u2) -> liftM Just (canonicalUnion u1 u2)
      (Just u1, Nothing) -> return (Just u1)
      (Nothing, Just u2) -> return (Just u2)
      (Nothing, Nothing) -> return Nothing
  otherwise -> return Nothing


-- ----------------------------------------------------------------------------
-- Utilities


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


-- TODO: This is guesswork.
intersectBrand :: EnvM m
               => String
               -> m [Field]
intersectBrand brand = do
  tys <- getBrandPath brand
  let f (TObject _ fs) = fs
      f t = error $ printf
              "intersectBrand: expected TObject in brand path, got %s"
              (renderType t)
  return (foldr overrideFields [] (map f tys))


sugarTObject :: EnvM m
             => Type
             -> m Type
sugarTObject (TObject brand fields) = do
  fields' <- intersectBrand brand
  return (TObject brand (overrideFields fields fields'))
sugarTObject ty = return ty


-- |Syntactic sugar for brands.  Theoretically, all the fields in an object
-- must be enumerated.  However, when a function is declared or a variable's
-- type is written, we fill in the fields that already exist in the brand
-- store.
brandSugar :: EnvM m
           => Type
           -> m Type
brandSugar ty = everywhereM (mkM sugarTObject) ty


unForall :: Type -> ([String], Type)
unForall (TNamedForall x t) = (x:xs, s)
  where (xs, s) = unForall t
unForall t = ([], t)
