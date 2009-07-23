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
  , isSubtype
  , canonize
  , canonicalUnion 
  -- * Interface to dataflow analysis
  -- $runtime
	, static
	, runtime
  -- * Utilities
  , fieldType
  ) where

import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.TypeDefinitions
import qualified Data.Set as S
import BrownPLT.TypedJS.Infrastructure


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


areSubtypes :: EnvM m
            => [Type]
            -> [Type]
            -> m Bool
areSubtypes [] [] = return True
areSubtypes (s:ss) (t:ts) = isSubtype s t +++ areSubtypes ss ts
areSubtypes _ _ = return False


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

-- |Assumes that the components are already canonized.
canonicalUnion :: EnvM m => Type -> Type -> m Type
canonicalUnion t1 t2 = do
  r <- isSubtype t1 t2
  case r of
    True -> return t1
    False -> do
      r <- isSubtype t2 t1
      case r of
        True -> return t2
        False -> case t1 < t2 of
          True -> return (TUnion t1 t2)
          False -> return (TUnion t2 t1)


-- Width and subsumption.  'canonize' handles permutations.
areFieldsSubtypes :: EnvM m
                  => [Field] -> [Field] -> m Bool
areFieldsSubtypes _ [] = return True
areFieldsSubtypes [] _ = return False
areFieldsSubtypes ((x1, ro1, t1):fs1) ((x2, ro2, t2):fs2)
  | x1 < x2 = areFieldsSubtypes fs1 ((x2, ro2, t2):fs2)
  | x1 == x2 = case (ro1, ro2) of
      (True, False) -> return False
      (False, False) -> return (t1 == t2) +++ areFieldsSubtypes fs1 fs2
      (_, True) -> isSubtype t1 t2 +++ areFieldsSubtypes fs1 fs2
  | otherwise = return False


-- |Assumes the arguments are in canonical forms.
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
  (TObject brand1 fs1, TObject brand2 fs2) -> -- TODO: support brands
    areFieldsSubtypes fs1 fs2
  (TApp c1 args1, TApp c2 args2) -> case c1 == c2 of
    True -> areSubtypes args1 args2
    False -> return False
  (TArguments (ArgType args1 optArg1), TArguments (ArgType args2 optArg2)) ->
    areSubtypes args1 args2 -- TODO: arity, blah blah blah
  (TArrow this1 args1 r1, TArrow this2 args2 r2) ->
    isSubtype this2 this1 +++
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
  otherwise -> 
    return False


-- ----------------------------------------------------------------------------
-- $runtime
-- Interface between the type system and the dataflow analysis


injRT :: RuntimeType -> RuntimeTypeInfo
injRT bt = TKnown (S.singleton bt)


runtime :: Type -> RuntimeTypeInfo
runtime t = case t of
  TId x -> error $ printf "TypeTheory.hs : argument of runtime contains \
                          \free type variable %s" x
  TIx _ -> TUnk
  TExists t -> runtime t
  TAny -> TUnk
  TApp "String" [] ->  injRT RTString
  TApp "Bool" [] ->  injRT RTBoolean
  TApp "Double" [] ->  injRT RTNumber
  TApp "Int" [] ->  injRT RTNumber
  TApp "Undefined" [] ->  injRT RTUndefined
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
  TAny -> case map flatStatic (S.toList rt) of
    [] -> return Nothing
    [t] -> return (Just t)
    (t:ts) -> liftM Just (foldM canonicalUnion t ts)
  TApp "String" [] | S.member RTString rt -> return (Just st)
  TApp "Bool" [] | S.member RTBoolean rt -> return (Just st)
  TApp "Double" [] | S.member RTNumber rt -> return (Just st)
  TApp "Int" [] | S.member RTNumber rt -> return (Just st)
  TApp "Undefined" [] | S.member RTUndefined rt -> return (Just st)
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
