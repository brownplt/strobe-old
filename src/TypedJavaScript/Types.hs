module TypedJavaScript.Types 
  ( Env
  , Kind (..)
  , KindEnv
  , freeTypeVariables
  , checkKinds
  , emptyEnv
 -- , argEnv
  , undefType
  , stringType
  , intType
  , doubleType
  , boolType
  , inferLit, refined
  , deconstrFnType
  , substType 
  , unRec
  , isSubType
  , unionType, unionTypeVP, equalityvp
  , gammaPlus, gammaMinus
  , checkTypeEnv
  , unaliasTypeEnv
  , unaliasType
  , Type (..)
  , VP (..)
  , TypeConstraint (..)
  , LatentPred (..)
  ) where

import Debug.Trace
import BrownPLT.JavaScript.Analysis.ANF
import TypedJavaScript.Prelude
import TypedJavaScript.PrettyPrint()
import qualified Data.Set as S
import qualified Data.Map as M

-- we don't want TJS expressions here
import TypedJavaScript.Syntax (Type (..), VP (..), Id(..),
  TypeConstraint(..), LatentPred(..))
-- but we do need the lits
import qualified TypedJavaScript.Syntax as TJS


-- |Kinds ensure that Array<int, int> and String<int> are illegal.  Our kind
-- definitions are more general than necessary.
data Kind 
  = KindStar
  | KindConstr [Kind] Kind
  deriving (Eq)


instance Show Kind where
  show KindStar = "*"
  show (KindConstr args r) = 
    concat (intersperse ", " (map show' args)) ++ " -> " ++ show r where
      -- parenthesize arrows on the left
      show' k = case k of 
        KindStar -> "*"
        KindConstr _ _ -> "(" ++ show k ++ ")"


type KindEnv = Map String Kind


assertKinds :: KindEnv -> (Type, Kind) -> Either String ()
assertKinds kinds (t, k) = do
  k' <- checkKinds kinds t
  unless (k' == k) $ do
    fail (printf "%s has kind %s, expected kind %s" (show t) (show k') (show k))


checkKinds :: Map String Kind -> Type -> Either String Kind
checkKinds kinds t = case t of
  TApp t ts -> do
    k <- checkKinds kinds t
    case k of
      KindConstr ks k 
        | length ks == length ts -> do
            mapM_ (assertKinds kinds) (zip ts ks)
            return k
        | otherwise -> fail "kind error (arg mismatch)"
      KindStar -> fail "kind error (expected * ... -> *)"
  TFunc args result _ -> do
    mapM_ (assertKinds kinds) (zip args (repeat KindStar))
    assertKinds kinds (result, KindStar)
    return KindStar
  TSequence args optional -> do
    mapM_ (assertKinds kinds) (zip args (repeat KindStar))
    case optional of
      Nothing -> return ()
      Just t -> assertKinds kinds (t, KindStar)
    return KindStar
  TId v -> case M.lookup v kinds of
    Just k -> return k
    Nothing -> fail $ printf "undeclared type %s" v
  TObject props -> do
    mapM_ (assertKinds kinds) (zip (map snd props) (repeat KindStar))
    return KindStar
  TAny -> return KindStar
  TRec id t -> do
    assertKinds (M.insert id KindStar kinds) (t, KindStar)
    return KindStar
  TUnion ts -> do
    mapM_ (assertKinds kinds) (zip ts (repeat KindStar))
    return KindStar
  TForall ids cs t -> do -- TODO: check constraints
    let kinds' = M.union (M.fromList (zip ids (repeat KindStar))) kinds
    assertKinds kinds' (t, KindStar)
    return KindStar
  TRefined t1 t2 -> do
    assertKinds kinds (t1, KindStar)
    assertKinds kinds (t2, KindStar)
    return KindStar


-- |Checks a type-environment for consistency, given a kind-environment.
-- Once the type-environment has passes this check, attempts to substitute
-- its aliases will always succeed.
checkTypeEnv :: KindEnv
             -> Map String Type
             -> Either String ()
checkTypeEnv kinds env = do
  -- Assume that all bindings are well-kinded.
  let kinds' = M.map (const KindStar) env
  let types = M.elems env
  -- Check each binding, assuming others are well-kinded.
  mapM_ (checkKinds (M.union kinds' kinds)) types


unaliasType :: KindEnv -> Map String Type
            -> Type
            -> Type
unaliasType kinds types type_ = case type_ of
  TId v -> case M.lookup v kinds of
    Just KindStar -> type_
    Just k -> error $ printf "unaliasType kindsTypeEnv: %s has kind %s" v 
                             (show k)
    Nothing -> case M.lookup v types of
      -- BrownPLT.TypedJS.IntialEnvironment.bindingFromIDL maps interfaces 
      -- named v to the type (TRec v ...).
      --
      -- No need for recursion, the lookup in types is recursive
      Just  t -> t
      Nothing -> error $ printf "unaliasType kindsTypeEnv: unbound type %s" v
  -- Stops infinite recursion
  TRec v t -> TRec v (unaliasType kinds (M.insert v (TId v) types) t)
  TAny -> TAny
  TObject props -> TObject (map unaliasProp props)
    where unaliasProp (v, t) = (v, unaliasType kinds types t)
  TSequence args vararg -> TSequence args' vararg' 
    where args' = map (unaliasType kinds types) args
          vararg' = case vararg of
            Nothing -> Nothing
            Just t -> Just (unaliasType kinds types t)
  TFunc args ret lp -> 
   TFunc args' ret' lp
    where args' = map (unaliasType kinds types) args
          ret' = unaliasType kinds types ret
  -- HACK: We do not allow constructors to be aliased.
  TApp t ts -> TApp t (map (unaliasType kinds types) ts)
  TUnion ts -> TUnion (map (unaliasType kinds types) ts)
  TRefined t1 t2 -> 
    TRefined (unaliasType kinds types t1) (unaliasType kinds types t2)
  TForall vs cs t -> TForall vs cs t' -- TODO: recur into cs?
    where types' = M.fromList (map (\v -> (v, TId v)) vs)
          t' = unaliasType kinds (M.union types' types) t

unaliasType' :: KindEnv -> Map String Type
            -> Type
            -> Type
unaliasType' kinds types type_ = case type_ of
  TId v -> case M.lookup v kinds of
    Just KindStar -> type_
    Just k -> error $ printf "unaliasType': %s has kind %s" v 
                             (show k)
    Nothing -> case M.lookup v types of
      -- BrownPLT.TypedJS.IntialEnvironment.bindingFromIDL maps interfaces 
      -- named v to the type (TRec v ...).
      Just  t -> TEnvId v
      Nothing -> error $ printf "unaliasType' kindsTypeEnv: unbound type %s" v
  -- Stops infinite recursion
  TRec v t -> TRec v (unaliasType' (M.insert v KindStar kinds) types t)
  TAny -> TAny
  TObject props -> TObject (map unaliasProp props)
    where unaliasProp (v, t) = (v, unaliasType' kinds types t)
  TSequence args vararg -> TSequence args' vararg' 
    where args' = map (unaliasType' kinds types) args
          vararg' = case vararg of
            Nothing -> Nothing
            Just t -> Just (unaliasType' kinds types t)
  TFunc args ret lp -> TFunc args' ret' lp
    where args' = map (unaliasType' kinds types) args
          ret' = unaliasType' kinds types ret
  -- HACK: We do not allow constructors to be aliased.
  TApp t ts -> TApp t (map (unaliasType' kinds types) ts)
  TUnion ts -> TUnion (map (unaliasType' kinds types) ts)
  TRefined t1 t2 -> 
    TRefined (unaliasType' kinds types t1) (unaliasType' kinds types t2)
  TForall vs cs t -> TForall vs cs t' -- TODO: recur into cs?
    where types' = M.fromList (map (\v -> (v, TId v)) vs)
          t' = unaliasType' kinds (M.union types' types) t

unaliasTypeEnv :: KindEnv
               -> Map String Type
               -> Map String Type
unaliasTypeEnv kinds aliasedTypes = types
  where explicitRec v t = unaliasType' kinds aliasedTypes t
          
        types = M.mapWithKey explicitRec aliasedTypes


freeTypeVariables :: Type -> Map String Kind
freeTypeVariables t = fv t where
  -- type variables in the constructor are applied
  fv (TApp _ ts) = M.unions (map fv ts)
  fv (TFunc args r _) = M.unions (map fv (r:args))
  fv (TSequence args Nothing) = M.unions (map fv args)
  fv (TSequence args (Just opt)) = M.unions (map fv (opt:args))
  fv (TId _) = M.empty
  fv (TObject props) = M.unions (map (fv.snd) props)
  fv TAny = M.empty
  fv (TRec id t) = M.insert id KindStar (fv t)
  fv (TUnion ts) = M.unions (map fv ts)
  fv (TForall ids _ t) = M.union (M.fromList (zip ids (repeat KindStar)))
                                 (fv t)
  fv (TRefined t1 t2) = M.union (fv t1) (fv t2)


--maps names to their type.
--ANF-generated variables have visible predicates.
type Env = Map String (Maybe (Type, VP))

emptyEnv :: Env
emptyEnv = M.empty

undefType :: Type
undefType = TId "undefined"

stringType = TId "string"

intType = TId "int"

doubleType = TId "double"

boolType = TId "bool"


-- |Deconstructs the declared type of a function, returning a list of quantified
-- variables, the types of each argument, and a return type.  As we enrich the
-- type-checker to handle more of a function type, include them here.
deconstrFnType :: Type 
               -> Maybe ([String], [TypeConstraint], [Type], Maybe Type, 
                         Type, LatentPred)
deconstrFnType (TRefined main refined) = deconstrFnType refined
deconstrFnType t@(TRec id t'@(TFunc{})) = -- Hack to avoid infinite recursion
  deconstrFnType (substType id t t')
deconstrFnType (TFunc args@(_:(TSequence _ vararg):_) result latentP) = 
  Just ([],[],args,vararg,result,latentP)
deconstrFnType _ = Nothing

unRec :: Type -> Type
unRec t@(TRec id t') = case t' of
  TId _ -> t' -- avoids infinite recursion
  otherwise -> unRec (substType id t t') -- handles rec x . rec y . ...
unRec t = t

-- |This is _not_ capture-free.
substType :: String -> Type -> Type -> Type
substType _ _ TAny = TAny
substType var sub (TRec var' t) 
  | var == var' = error "substType captures"
  | otherwise   = TRec var' (substType var sub t)
substType var sub (TForall formals constraints body)  -- TODO: Subst into?
  | var `elem` formals = TForall formals constraints body
  | otherwise = TForall formals constraints (substType var sub body)
substType var sub (TApp constr args) = 
  TApp constr (map (substType var sub) args)
substType var sub (TUnion ts) = 
  TUnion (map (substType var sub) ts)
substType var sub (TId var')
  | var == var' = sub
  | otherwise =  TId var'
substType var sub (TSequence args vararg) = 
  TSequence (map (substType var sub) args)
            (liftM (substType var sub) vararg)
substType var sub (TFunc args ret latentP) =
  TFunc (map (substType var sub) args)
        (substType var sub ret)
        latentP
substType var sub (TObject fields) =
  TObject (map (\(v,t) -> (v,substType var sub t)) fields)
substType var sub (TEnvId x) = TEnvId x -- this is most certainly wrong.
substType _ _ (TRefined _ _) = error "substType TRefined NYI"



-- |Infers the type of a literal value.  Used by the parser to parse 'literal
-- expressions in types
inferLit :: Monad m 
         => TJS.Expression SourcePos
         -> m (Type)
inferLit (TJS.StringLit p _) = return (TId "string")
inferLit (TJS.NumLit p _) = return (TId "double")
inferLit (TJS.IntLit p _) = return (TId "int")
inferLit (TJS.BoolLit p _) = return (TId "bool")
inferLit expr =
  fail $ "Cannot use as a literal"

-- This definition of '(<:)' is for internal use only.  It assumes there are no
-- additional constraints.  It should not be exported as the type-checker must
-- check for subtypes in the presence of user-specified constraints.
--
-- The functions that use this (gammaPlus, gammaMinux, unionTypeVP) may need
-- to take an additional list of constraints.
x <: y = isSubType M.empty [] x y


assert :: Bool -> Maybe ()
assert False = Nothing
assert True = Just ()

anyM :: (a -> b -> Maybe a) -> a -> [b] -> Maybe a
anyM _ a [] = Nothing
anyM f a (b:bs) = case f a b of
  Nothing -> anyM f a bs
  Just a  -> return a

{-
eq :: Set (Type, Type)
   -> (Type, Type)
   -> Maybe (Set (Type, Type))
eq rel (t1, t2)
  | (t1, t2) `S.member` rel = return rel
  | otherwise case (t1, t2) of
    (TId x, TId y) 
      | x == y   -> return rel
      | otherwise -> fail $ printf "%s is not a subtype of %s" x y
    (TRefined declared1 refined1, TRefined declared2 refined2) -> do
      rel <- eq (S.insert (t1, t2) rel) refined1 refined2
      eq rel declared1 declared2
    (TApp c1 args1, TApp c2 args2) -> do
      assert (length args1 == length args2)
      rel <- eq (S.insert (t1, t2) rel) c1 c2
      foldM eq rel (zip arg1 args2)
    (TFunc req2 Nothing ret2 lp2, TFunc req1 Nothing ret1 lp1) -> do
      assert (length req2 == length req1)
      assert (lp1 == lp2)
      rel <- eq (S.insert (t1, t2) rel) (ret2, ret1)
      foldM eq rel (zip req1 req2)
    (TForall ids1 tcs1 t1, TForall ids2 tcs2 t2) -> do
      assert (ids1 == ids2)
      assert (tcs1 == tcs2)
      eq (S.insert (t1, t2) rel) (t1, t2)
    (TObject _ props1, TObject _ props2) -> do
      let prop rel ((id1, t1), (id2, t2)) = do
            assert (id1 == id2)
            eq rel (t1, t2)
      foldM prop (S.insert (t1, t2) rel) (zip props1 prop2)
    (TUnion ts1, t2) -> do
      foldM (\rel t1 -> st env rel (t1, t2)) rel ts1 -- all
    (t1, TUnion ts2) -> do
      anyM (\rel t2 -> st env rel (t1, t2)) rel ts2
    (t1, TRec v t2') -> do
      st env (S.insert (t1, t2) rel) (t1, substType v t2 t2')
    (TRec v t1', t2) -> do
      st env (S.insert (t1, t2) rel) (substType v t1 t1', t2)
    otherwise -> fail $ printf "%s is not a subtype of %s" (show t1) (show t2)
-}

st :: Map String Type  -- ^type environment
   -> Set (Type, Type) -- ^assumed subtypes
   -> (Type, Type) -- ^we are checking if lhs <: rhs      
   -> Maybe (Set (Type, Type)) -- ^returns an extended set of assumptions if
                               -- ^lhs <: rhs
st env rel (t1, t2)
  | (t1, t2) `S.member` rel = return rel
  | otherwise = do
   case (t1, t2) of
    -- If x == y, then (env ! x) == (env ! y), so t1 <: t2
    (TEnvId x, TEnvId y) | x == y -> return rel
    -- However, if x != y, they may still be structurally equivalent.
    (TEnvId x, _) -> case M.lookup x env of
      Just t1' -> st env rel (t1', t2)
      Nothing -> error $ printf "BrownPLT.TypedJS.Subtypes.st: TEnvId %s is \
                                \not in the environment. TEnvId x <: t2" x
    (_, TEnvId y) -> case M.lookup y env of
      Just t2' -> st env rel (t1, t2')
      Nothing -> error $ printf "BrownPLT.TypedJS.Subtypes.st: TEnvId %s is \
                                \not in the environment. t1 <: TEnvId y" y

    (_, TAny) -> return (S.insert (t1, t2) rel)
    (TId "int", TId "double") -> return rel
    (_, TId "any") -> return rel
    (TId x, TId y) 
      | x == y   -> return rel
      | otherwise -> fail $ printf "%s is not a subtype of %s" x y
    (TRefined declared1 refined1, TRefined declared2 refined2) ->
      st env (S.insert (t1, t2) rel) (refined1, declared2)
    (TRefined declared refined, other) ->
      st env (S.insert (t1, t2) rel) (refined, other)
    (other, TRefined declared refined) -> 
      st env (S.insert (t1, t2) rel) (other, declared)
    (TApp c1 args1, TApp c2 args2) -> do
      assert (length args1 == length args2)
      -- assert (c1 == c2)
      -- assert (args1 == args2)
      -- return rel
      rel <- st env (S.insert (t1, t2) rel) (c1, c2)
      foldM (st env) rel (zip args1 args2) 
    --temporary not-quite-good subtyping for vararity functions:
    (TSequence args1 Nothing, TSequence args2 Nothing) -> do
      assert (length args1 == length args2)
      foldM (st env) rel (zip args1 args2)
    (TSequence args1 (Just v1), TSequence args2 (Just v2)) -> do
      assert (length args1 == length args2)
      foldM (st env) rel (zip (v1:args1) (v2:args2))
    (TFunc args2 ret2 lp2, TFunc args1 ret1 lp1) -> do
      assert (lp1 == lp2 || lp1 == LPNone)
      rel <- st env (S.insert (t1, t2) rel) (ret2, ret1)
      foldM (st env) rel (zip args1 args2)
    (TForall ids1 tcs1 t1, TForall ids2 tcs2 t2) -> do
      assert (ids1 == ids2)
      assert (tcs1 == tcs2)
      st env (S.insert (t1, t2) rel) (t1, t2)
    (TObject props1, TObject props2) -> do
      -- All of props2 must be in props1
      let prop rel (id2, t2) = do
            t1 <- lookup id2 props1
            st env rel (t1, t2)
      foldM prop (S.insert (t1, t2) rel) props2
    (t1, TRec v t2') -> do
      rez <- st env (S.insert (t1, t2) rel) (t1, substType v t2 t2')
      return rez
    (TRec v t1', t2) -> do
      rez <- st env (S.insert (t1, t2) rel) (substType v t1 t1', t2)
      return rez
    --special-case: arrays are subtypes of sequences.
    --eventually remove this once we make arrays actually sequences.
    (TApp (TId "Array") [arrt], TSequence [] (Just seqt)) -> do
      st env (S.insert (t1, t2) rel) (arrt, seqt)
    (TSequence [] (Just seqt), TApp (TId "Array") [arrt]) -> do
      st env (S.insert (t1, t2) rel) (seqt, arrt)
    (TUnion ts1, t2) -> do
      foldM (\rel t1 -> st env rel (t1, t2)) rel ts1 -- all
    (t1, TUnion ts2) -> do
      anyM (\rel t2 -> st env rel (t1, t2)) rel ts2
    otherwise -> fail $ printf "%s is not a subtype of %s" (show t1) (show t2)


isSubType :: Map String Type
          -> [TypeConstraint] -> Type -> Type
          -> Bool
isSubType env cs t1 t2 = result where
  result = case st env initial (t1, t2) of
    Just _ -> True
    Nothing -> False
  initial = S.fromList (map subtype cs)
  subtype (TCSubtype s t) = (s, t)


unionType :: Maybe (Type) 
          -> Maybe (Type)
          -> Maybe (Type)
unionType Nothing Nothing = error "unionType called with 2 Nothings"
unionType Nothing (Just t) = Just $ TUnion [undefType, t]
unionType (Just t) Nothing = Just $ TUnion [t, undefType]
unionType (Just t1) (Just t2)
  | t1 <: t2 = Just t2
  | t2 <: t1 = Just t1
  | otherwise = Just (TUnion [t1, t2]) -- TODO: What?

-- keep the VPs that are the same
-- TODO: something like VPLit 3 "int", VPLit 4 "int" might be salvageable.
-- TODO: rename this function
takeEquals :: VP -> VP -> VP
takeEquals (VPMulti v1s) (VPMulti v2s) = VPMulti (zipWith takeEquals v1s v2s)
takeEquals (VPMulti v1s) v2 = VPMulti (map (takeEquals v2) v1s)
takeEquals v1 (VPMulti v2s) = VPMulti (map (takeEquals v1) v2s)
takeEquals (VPType t1 id1) (VPType t2 id2) = 
  if id1 == id2 then (VPType (TUnion [t1, t2]) id1) else VPNone
takeEquals v1 v2 = if v1 == v2 then v1 else VPNone

unionTypeVP :: Maybe (Type, VP)
            -> Maybe (Type, VP)
            -> Maybe (Type, VP)
unionTypeVP Nothing Nothing = Nothing
unionTypeVP Nothing (Just (t, v)) = Just (TUnion [undefType, t], VPNone)
unionTypeVP (Just (t, v)) Nothing = Just (TUnion [t, undefType], VPNone)
unionTypeVP (Just (t1, vp1)) (Just (t2, vp2)) = 
  case unionType (Just t1) (Just t2) of
    Nothing -> Nothing
    Just t  -> Just (t, takeEquals vp1 vp2)
flattenUnion :: (Type) -> (Type)
flattenUnion (TUnion ts) = 
	case (foldl (\res t -> case t of 
                       TUnion tocomb -> res ++ tocomb
                       regular -> res ++ [regular])
                    [] ts) of
          [onet] -> onet
          noneormanyt -> TUnion noneormanyt

flattenUnion  t = t


-- Helpers for occurrence typing, from TypedScheme paper
restrict :: (Type) -> (Type) -> (Type)
restrict (TRefined main ref) t = case restrict ref t of
  TRefined _ reallyrefined -> TRefined main reallyrefined
  reallyrefined -> TRefined main reallyrefined
restrict s t
 | s <: t = s
 | otherwise = case t of
     --TODO: make sure TRefined-ness deals well with the following case:
     TUnion ts -> flattenUnion $ 
                        TUnion (map (restrict s) ts)
     --TODO: make sure restrict is correct; this is different than
     --the typed scheme paper
     --TODO: make sure returning a TRefined here is correct
     _ -> let rez = flattenUnion $
                      TUnion (filter (\hm -> hm <: t)
                                     (case s of
                                        TUnion ts -> ts
                                        _ -> [s]))
           in case rez of 
                TUnion [] -> TRefined s t
                _ -> TRefined s rez

remove :: (Type) -> (Type) -> (Type)
remove (TRefined main ref) t = case remove ref t of
  TRefined _ reallyrefined -> TRefined main reallyrefined
  reallyrefined -> TRefined main reallyrefined
remove s t
 | s <: t = TUnion  []
 | otherwise = case t of
     TUnion ts -> flattenUnion $ 
                        TUnion (map (remove s) ts)
     --TODO: make sure remove is correct; this is different than
     --the typed scheme paper
     _ -> TRefined s $ flattenUnion $ 
            TUnion  
                   (filter (\hm -> not $ hm <: t)
                           (case s of
                             TUnion ts -> ts
                             _ -> [s]))
     
gammaPlus :: Env -> VP -> Env
gammaPlus env (VPType t v) =  case M.lookup v env of
  Nothing -> env
  Just Nothing -> env
  Just (Just (t', vp_t)) -> M.insert v (Just (restrict t' t, vp_t)) env
-- if (x), when true, removes all things from x that are like "undefined"
--gammaPlus g (VPId x) = gammaMinus g (VPType (TId noPos "undefined") x)
gammaPlus g (VPNot vp) = gammaMinus g vp
gammaPlus g (VPMulti vs) = foldl gammaPlus g vs
gammaPlus g _ = g

gammaMinus :: Env -> VP -> Env
gammaMinus env (VPType t v) = case M.lookup v env of
  Nothing -> env
  Just Nothing -> env
  Just (Just (t', vp_t)) -> M.insert v (Just (remove t' t, vp_t)) env
-- if (x), when false, leaves only things in x that are like "undefined"
--gammaMinus g (VPId x) = gammaPlus g (VPType (TId noPos "undefined") x)
gammaMinus g (VPNot vp) = gammaPlus g vp
gammaMinus g (VPMulti vs) = foldl gammaMinus g vs
gammaMinus g _ = g

asBool :: forall a. Lit a -> Bool
asBool l = case l of
  StringLit _ s -> s == ""
  RegexpLit{}   -> True
  NumLit _ n    -> n == 0.0
  IntLit _ i    -> i == 0
  BoolLit _ b   -> b
  NullLit{}     -> False
  ArrayLit{}    -> True
  ObjectLit{}   -> True
  FuncLit{}     -> True

-- combine two VPs into a third, happens with == sign.
equalityvp :: VP -> VP -> VP
-- x == 4
-- typeof x == "number"
equalityvp (VPTypeof x) (VPLit (StringLit l s) (TId "string")) = case s of
  "number"    -> VPType (TId "double") x
  "undefined" -> VPType undefType x
  "boolean"   -> VPType (TId "bool") x
  "string"    -> VPType (TId "string") x
  "function"  -> 
    VPType (TFunc [TUnion [], TSequence [] Nothing] (TId "any") LPNone) x
  "object"    -> error "vp for typeof x == 'object' nyi"
  _           -> VPNone
equalityvp a@(VPLit (StringLit l s) (TId "string")) b@(VPTypeof x) = 
  equalityvp b a

-- yay for cartesian product.
-- this could be done implicitly from the other equalityvp definition, but
-- then we'd have nested VPMultis. doesn't really matter.
equalityvp (VPMulti v1) (VPMulti v2) = 
  VPMulti (nub [equalityvp a b | a <- v1, b <- v2])               
equalityvp a (VPMulti vs) = 
  VPMulti (map (equalityvp a) vs)
equalityvp a@(VPMulti{}) b = equalityvp b a

equalityvp _ _ = VPNone

refined :: Type -> Type
refined (TRefined main ref) = ref
refined t = t  
