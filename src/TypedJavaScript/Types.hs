module TypedJavaScript.Types 
  ( Env
  , Kind (..)
  , KindEnv
  , checkKinds
  , emptyEnv
 -- , argEnv
  , undefType
  , stringType
  , intType
  , doubleType
  , boolType
  , inferLit
  , deconstrFnType
  , substType 
  , unRec
  , isSubType
  , unionType, unionTypeVP, unionThisTypeVP
  , checkTypeEnv
  , unaliasTypeEnv
  , unaliasType, realiasType
  , Type (..)
  , TypeConstraint (..)
  , LatentPred (..)
  , flattenUnion
  ) where

import BrownPLT.JavaScript.Analysis.ANF
import TypedJavaScript.Prelude
import TypedJavaScript.PrettyPrint()
import qualified Data.Set as S
import qualified Data.Map as M

-- we don't want TJS expressions here
import TypedJavaScript.Syntax (Type (..), TypeConstraint(..), LatentPred(..),
  Access(..))
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
  TApp s ts -> case M.lookup s kinds of
    Just (KindConstr ks k)
      | length ks == length ts -> do
          mapM_ (assertKinds kinds) (zip ts ks)
          return k
      | otherwise -> fail "kind error (arg mismatch)"
    Just KindStar -> fail "kind error (expected * ... -> *)"
    Nothing -> fail $ printf "undefined type constructor %s" s
  TFunc _ args result _ -> do
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
  TObject _ _ props -> do
    mapM_ (assertKinds kinds) (zip (map cadr props)(repeat KindStar))
    return KindStar
  TAny -> return KindStar
  TRec id t -> do
    assertKinds (M.insert id KindStar kinds) (t, KindStar)
    return KindStar
  TUnion ts -> do
    mapM_ (assertKinds kinds) (zip ts (repeat KindStar))
    return KindStar
  TForall ids cs t -> do
    let kinds' = M.union (M.fromList (zip ids (repeat KindStar))) kinds
    assertKinds kinds' (t, KindStar)
    return KindStar
  TEnvId id -> return KindStar

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
  TEnvId id -> type_
  TId v -> case M.lookup v kinds of
    Just KindStar -> type_
    Just k -> error $ printf "unaliasType kindsTypeEnv: %s has kind %s" v 
                             (show k)
    Nothing -> case M.lookup v types of
      -- BrownPLT.TypedJS.IntialEnvironment.bindingFromIDL maps interfaces 
      -- named v to the type (TRec v ...).
      Just  t -> TEnvId v
      Nothing -> error $ printf "unaliasType kindsTypeEnv: unbound type %s" v
  -- Stops infinite recursion
  TRec v t -> TRec v (unaliasType kinds (M.insert v (TId v) types) t)
  TAny -> TAny
  TObject hasSlack isOp props -> TObject hasSlack isOp (map unaliasProp props)
    where unaliasProp (v, (t, x)) = (v, (unaliasType kinds types t, x))
  TSequence args vararg -> TSequence args' vararg' 
    where args' = map (unaliasType kinds types) args
          vararg' = case vararg of
            Nothing -> Nothing
            Just t -> Just (unaliasType kinds types t)
  TFunc ptype args ret lp -> 
   TFunc ptype' args' ret' lp
    where args' = map (unaliasType kinds types) args
          ret' = unaliasType kinds types ret
          ptype' = case ptype of
                     Nothing -> Nothing
                     Just t  -> Just $ unaliasType kinds types t
  TApp s ts -> TApp s (map (unaliasType kinds types) ts)
  TUnion ts -> TUnion (map (unaliasType kinds types) ts)
  TForall vs cs t -> TForall vs cs t' -- TODO: recur into cs?
    where types' = M.fromList (map (\v -> (v, TId v)) vs)
          t' = unaliasType kinds (M.union types' types) t


unaliasTypeEnv :: KindEnv
               -> Map String Type
               -> Map String Type
unaliasTypeEnv kinds aliasedTypes = types
  where explicitRec v t = unaliasType kinds aliasedTypes t
        types = M.mapWithKey explicitRec aliasedTypes

--TODO: fill this function in. 
realiasType :: Map String Type -> Type
            -> Type
realiasType types type_ = case type_ of
  _ -> type_

--maps names to (declared type, actual type, vp)
type Env = Map String (Maybe (Type, Type, Bool))

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
                         Either Type Type, LatentPred, Maybe Type)
deconstrFnType t@(TRec id t'@(TFunc{})) = -- Hack to avoid infinite recursion
  deconstrFnType (substType id t t')
--function:
deconstrFnType (TFunc Nothing args@(_:(TSequence _ vararg):_) result latentP) = 
  Just ([],[],args,vararg,Left result,latentP, Nothing)
deconstrFnType (TForall ids cs 
                        (TFunc Nothing args@(_:(TSequence _ vararg):_) r lp))=
  Just (ids, cs, args, vararg, Left r, lp, Nothing)
--constructor:
deconstrFnType (TFunc (Just pt) args@(_:(TSequence _ vararg):_) result latentP)=
  Just ([],[],args,vararg,Right result,latentP, (Just pt))
deconstrFnType (TForall ids cs 
                        (TFunc (Just pt) args@(_:(TSequence _ vararg):_) r lp))=
  Just (ids, cs, args, vararg, Right r, lp, (Just pt))
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
substType var sub (TFunc isC args ret latentP) =
  TFunc isC
        (map (substType var sub) args)
        (substType var sub ret)
        latentP
substType var sub (TObject hasSlack isOpen fields) =
  TObject hasSlack isOpen (map (\(v,(t,x)) -> (v,(substType var sub t,x))) 
                               fields)
substType var sub (TEnvId x) = TEnvId x -- this is most certainly wrong.

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
x <: y = isSubType M.empty [] x y


assert :: Bool -> Maybe ()
assert False = Nothing
assert True = Just ()

anyM :: (a -> b -> Maybe a) -> a -> [b] -> Maybe a
anyM _ a [] = Nothing
anyM f a (b:bs) = case f a b of
  Nothing -> anyM f a bs
  Just a  -> return a

st :: Map String Type  -- ^type environment
   -> Set (Type, Type) -- ^assumed subtypes
   -> (Type, Type) -- ^we are checking if lhs <: rhs      
   -> Maybe (Set (Type, Type)) -- ^returns an extended set of assumptions if
                               -- ^lhs <: rhs
st env rel (t1, t2)
  | (t1, t2) `S.member` rel = return rel
  | otherwise = do
   case (t1, t2) of
    --titerator is actually a string!
    (TIterator _, TId "string") -> return rel
    (TId "string", TIterator _) -> return rel
    (TApp "Array" _, TObject True _ [("length", (TId "int", _))]) -> return rel
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
    (TId "int", TId "double") -> return rel
    (_, TAny) -> return (S.insert (t1, t2) rel)
    (TId x, TId y) 
      | x == y   -> return rel
{-      | otherwise -> --fail $ printf "%s is not a subtype of %s" x y
      --temporary hack: if the TId is in the env, then look it up -}
         
          
    (TApp c1 args1, TApp c2 args2) -> do
      assert (length args1 == length args2)
      assert (c1 == c2)
      foldM (st env) rel (zip args1 args2) 
    
    (TSequence args1 vararg, TSequence args2 Nothing) -> do
      --assuming "t2 = t1":
      
      --it's fine if t1 is bigger, since the ones the lhs can access
      --will still work. might change this for func calls later.  but
      --we can never give it less, because then args2 could assign
      --into stuff that doesn't exist for args1.  this wouldn't
      --actually break anything in JS, since we don't have arrays of
      --limited size, so maybe this should be changed.
      --bug if args1 has varargs, they should repeat to fill the gap.
      let args2' = case vararg of
                     Nothing -> args1
                     Just vt -> args1 ++ (take (length args2 - length args1)
                                               (repeat vt))

      foldM (st env) rel (zip args1 args2')
    (TSequence args1 Nothing, TSequence args2 (Just vararg2)) -> do
      Nothing --fail, since args2 could access more than args1 has(?)
    (TSequence args1 (Just vararg1), TSequence args2 (Just vararg2)) -> do
      --TODO: add test cases for this case
      --check everything up to the varargs:
      let (args1', args2')
            | length args1 >= length args2 = 
                (args1, args2 ++ (take (length args1 - length args2)
                                       (repeat vararg2)))
            | otherwise = 
                (args1 ++ (take (length args2 - length args1)
                                (repeat vararg1)), args2)      
      rel' <- foldM (st env) (S.insert (t1, t2) rel) (zip args1' args2')
      --now check the varargs
      st env rel' (vararg1, vararg2)

    (TFunc pt2 args2 ret2 lp2, TFunc pt1 args1 ret1 lp1) -> do
      
      --when (isJust pt2 || isJust pt1) (fail "constr subtype NYI")
      assert (lp1 == lp2 || lp1 == LPNone)
      rel <- st env (S.insert (t1, t2) rel) (ret2, ret1)
      rez <- foldM (st env) rel (zip args1 args2)
      case (isJust pt2, isJust pt1) of
        (True, True) -> st env rez (fromJust pt2, fromJust pt1)
        (False, True) -> fail "func is not subtype of constructor"
        (True, False) -> fail "constructor is not subtype of funtcion"
        (False, False) -> Just rez
      
    (TForall ids1 tcs1 t1, TForall ids2 tcs2 t2) -> do
      assert (ids1 == ids2)
      assert (tcs1 == tcs2)
      st env (S.insert (t1, t2) rel) (t1, t2)

    --open objects are subtypes of closed or open objects, but thats
    --it for sub-typing open objects.    
    (TObject slack1 open1 props1, TObject slack2 open2 props2) -> do    
      -- if prop2 is readable, prop1 must be readable and a subtype
      -- if prop2 is writable, prop1 must be writable and a supertype
      let prop2prop rel (id1, (t1, (r1, w1))) (id2, (t2, (r2, w2))) = do
            rel' <- doRead rel (t1, r1) (t2, r2)
            doWrite rel' (t1, w1) (t2, w2)            
          doRead rel (t1, r1) (t2, r2) = if r2 
            then if not r1
              then fail "readability mismatch"  
              else st env rel (t1, t2)
            else return rel
          doWrite rel (t1, w1) (t2, w2) = if w2 
            then if not w1
              then fail "writability mismatch"
              else st env rel (t2, t1)
            else return rel
      
            
      case ((slack1, open1, props1), (slack2, open2, props2)) of 
        --if there's slack in the first object, all of props2 must be
        --in props1
        ((True, False, props1), (_, _, props2)) -> do
          let prop rel (id2, (t2, (r2, w2))) = do
                (t1,(r1, w1)) <- lookup id2 props1
                prop2prop rel (id2, (t1, (r1, w1))) (id2, (t2, (r2, w2)))
          foldM prop (S.insert (t1, t2) rel) props2
        
        --if there's slack in the second object... it doesn't have to have
        --all of props2, as those will be accounted for in the slack.
        ((False, False, props1), (True, _, props2)) -> do
          let prop rel (id2, (t2,x2)) = case lookup id2 props1 of
                Nothing -> return rel
                Just (t1,x1) -> prop2prop rel (id2, (t1, x1)) (id2, (t2, x2))
          foldM prop (S.insert (t1, t2) rel) props2

        --if there's no slack on either one, we must be invariant:          
        ((False, False, props1), (False, _, props2)) -> do
          let fields1 = S.fromList (map fst props1)
          let fields2 = S.fromList (map fst props2)
          let prop rel (id2, (t2, (r2, w2))) = do
                (t1,(r1, w1)) <- lookup id2 props1
                prop2prop rel (id2, (t1, (r1, w1))) (id2, (t2, (r2, w2)))
          case S.null (S.difference fields1 fields2) of
            True -> foldM prop (S.insert (t1, t2) rel) props2
            False -> fail "subtyping: invariant objects"

    (t1, TRec v t2') -> do
      rez <- st env (S.insert (t1, t2) rel) (t1, substType v t2 t2')
      return rez
    (TRec v t1', t2) -> do
      rez <- st env (S.insert (t1, t2) rel) (substType v t1 t1', t2)
      return rez
    (TUnion ts1, t2) -> do
      foldM (\rel t1 -> st env rel (t1, t2)) rel ts1 -- all
    (t1, TUnion ts2) -> do
      anyM (\rel t2 -> st env rel (t1, t2)) rel ts2

    --temporary hack: if the TId is in the env, then look it up -}
    (TId x, _) -> case M.lookup x env of
      Just t1' -> st env rel (t1', t2)
      Nothing -> Nothing
    (_, TId y) -> case M.lookup y env of
      Just t2' -> st env rel (t1, t2')
      Nothing -> Nothing

    otherwise -> fail $ printf "%s is not a subtype of %s" (show t1) (show t2)



isSubType :: Map String Type
          -> [TypeConstraint] -> Type -> Type
          -> Bool
isSubType env cs t1 t2 = result where
  result = case st env initial (t1, t2) of
    Just _ -> True
    Nothing -> False
  initial = S.fromList (map subtype cs)
  subtype (TCSubtype v t) = (TId v, t)

unionType :: Type -> Type -> Type
unionType t1 t2
  | t1 <: t2 = t2
  | t2 <: t1 = t1
  | otherwise = TUnion [t1, t2]

--treat 'this' as if t1 and t2 were environments
unionThisType (TObject s o p1) (TObject _ _ p2) = TObject s o $ 
  map (\(id,ma) -> case ma of
         Nothing -> (id,(undefType, (True, True))) --TODO: access??
         Just t  -> (id,(t, (True, True)))) $
    M.toList (M.unionWith (\ma mb -> do
      a <- ma
      b <- mb
      return $ unionType a b) 
      (M.fromList (map (\(a,(b,x)) -> (a, Just b)) p1))
      (M.fromList (map (\(a,(b,x)) -> (a, Just b)) p2)))
unionThisType a b = unionType a b --if we're not in a constructor

unionTypeVP :: Maybe (Type, Type, Bool)
            -> Maybe (Type, Type, Bool)
            -> Maybe (Type, Type, Bool)
unionTypeVP Nothing Nothing = Nothing
unionTypeVP Nothing (Just (t, tact, b)) = Just (t, tact, b)
unionTypeVP (Just (t, tact, b)) Nothing = Just (t, tact, b)
unionTypeVP (Just (t1, t1act, b1)) (Just (t2, t2act, b2)) =
  if b1 /= b2 
    then error "OMG"
    else Just (unionType t1 t2, unionType t1act t2act, b1) 


unionThisTypeVP :: (Type, Type, Bool)
              -> (Type, Type, Bool)
              -> (Type, Type, Bool)
unionThisTypeVP (td1, ta1, b1) (td2, ta2, b2) =
  (unionThisType td1 td2, unionThisType ta1 ta2, b1) 


flattenUnion :: (Type) -> (Type)
flattenUnion (TUnion ts) = 
	case (foldl (\res t -> case t of 
                       TUnion tocomb -> res ++ tocomb
                       regular -> res ++ [regular])
                    [] ts) of
          [onet] -> onet
          noneormanyt -> TUnion noneormanyt

flattenUnion  t = t
