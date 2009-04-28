module TypedJavaScript.Types 
  ( Env
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
  ) where

--import qualified BrownPLT.JavaScript.Analysis.ANF as ANF
import System.IO.Unsafe --unsafePerformIO

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

p = initialPos "TypedJavaScript.Types"

data Kind 
  = KindStar
  | KindConstr [Kind] Kind       

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
               -> Maybe ([String], [TypeConstraint], [Type], Type, LatentPred)
deconstrFnType (TRefined main refined) = deconstrFnType refined
deconstrFnType t@(TRec id t'@(TFunc{})) = -- Hack to avoid infinite recursion
  deconstrFnType (substType id t t')
deconstrFnType (TFunc args _ result latentP) = 
  Just ([],[],args,result,latentP)
deconstrFnType (TForall ids constraints (TFunc args _ result latentP)) = 
  Just (ids,constraints,args,result,latentP)
deconstrFnType _ = Nothing

unRec :: Type -> Type
unRec t@(TRec id t') = case t' of
  TId _ -> t' -- avoids infinite recursion
  otherwise -> unRec (substType id t t') -- handles rec x . rec y . ...
unRec t = t

-- |This is _not_ capture-free.
substType :: String -> Type -> Type -> Type
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
substType var sub (TFunc args vararg ret latentP) =
  TFunc (map (substType var sub) args)
        (liftM (substType var sub) vararg)
        (substType var sub ret)
        latentP
substType var sub (TObject fields) =
  TObject (map (\(v,t) -> (v,substType var sub t)) fields)
substType _ _ (TRefined _ _) = error "substType TRefined NYI"

applyType :: Monad m => SourcePos -> Type -> [Type] -> m (Type) -- TODO: ensure constraints
applyType loc (TRefined x y) actuals = applyType loc y actuals
applyType loc (TForall formals constraints body) actuals = do
  unless (length formals == length actuals) $ do
    fail $ printf "at %s: quantified type has %s vars but %s were supplied"
            (show loc) (show (length formals)) (show (length actuals)) 
  return $ foldr (uncurry substType) body (zip formals actuals)
applyType loc t [] = return t
applyType loc t actuals =
  fail $ printf ("at %s: type %s is not quantified, but %s " ++ 
                 " type arguments were supplied") (show t)
                   (show (length actuals))


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
x <: y = isSubType [] x y


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
      foldM (\rel t1 -> st rel (t1, t2)) rel ts1 -- all
    (t1, TUnion ts2) -> do
      anyM (\rel t2 -> st rel (t1, t2)) rel ts2
    (t1, TRec v t2') -> do
      st (S.insert (t1, t2) rel) (t1, substType v t2 t2')
    (TRec v t1', t2) -> do
      st (S.insert (t1, t2) rel) (substType v t1 t1', t2)
    otherwise -> fail $ printf "%s is not a subtype of %s" (show t1) (show t2)
-}

--how to 'printf':      tmp <- seq (unsafePerformIO $ putStrLn $ "In the trec: " ++ show (t1,t2) ++ " -> " ++ show (t1, substType v t2 t2')) (return rel)

-- based on TAPL p.305
st :: Set (Type, Type)
   -> (Type, Type)
   -> Maybe (Set (Type, Type))
st rel (t1, t2)
  | (t1, t2) `S.member` rel = return rel
  | otherwise = do
   case (t1, t2) of
    (_, TAny) -> return (S.insert (t1, t2) rel)
    (TId "int", TId "double") -> return rel
    (_, TId "any") -> return rel
    (TId x, TId y) 
      | x == y   -> return rel
      | otherwise -> fail $ printf "%s is not a subtype of %s" x y
    (TRefined declared1 refined1, TRefined declared2 refined2) ->
      st (S.insert (t1, t2) rel) (refined1, declared2)
    (TRefined declared refined, other) ->
      st (S.insert (t1, t2) rel) (refined, other)
    (other, TRefined declared refined) -> 
      st (S.insert (t1, t2) rel) (other, declared)
    (TApp c1 args1, TApp c2 args2) -> do
      assert (length args1 == length args2)
      -- assert (c1 == c2)
      -- assert (args1 == args2)
      -- return rel
      rel <- st (S.insert (t1, t2) rel) (c1, c2)
      foldM st rel (zip args1 args2) 
    (TFunc req2 Nothing ret2 lp2, TFunc req1 Nothing ret1 lp1) -> do
      assert (length req2 == length req1)
      assert (lp1 == lp2 || lp1 == LPNone)
      rel <- st (S.insert (t1, t2) rel) (ret2, ret1)
      foldM st rel (zip req1 req2)
    (TForall ids1 tcs1 t1, TForall ids2 tcs2 t2) -> do
      assert (ids1 == ids2)
      assert (tcs1 == tcs2)
      st (S.insert (t1, t2) rel) (t1, t2)
    (TObject props1, TObject props2) -> do
      -- All of props2 must be in props1
      let prop rel (id2, t2) = do
            t1 <- lookup id2 props1
            st rel (t1, t2)
      foldM prop (S.insert (t1, t2) rel) props2
    (t1, TRec v t2') -> do
      rez <- st (S.insert (t1, t2) rel) (t1, substType v t2 t2')
      return rez
    (TRec v t1', t2) -> do
      rez <- st (S.insert (t1, t2) rel) (substType v t1 t1', t2)
      return rez
    (TUnion ts1, t2) -> do
      foldM (\rel t1 -> st rel (t1, t2)) rel ts1 -- all
    (t1, TUnion ts2) -> do
      anyM (\rel t2 -> st rel (t1, t2)) rel ts2
    otherwise -> fail $ printf "%s is not a subtype of %s" (show t1) (show t2)

isSubType :: [TypeConstraint] -> Type -> Type
          -> Bool
isSubType cs t1 t2 = result where
  result = case st initial (t1, t2) of
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
     
--TODO: in TS, 'false' is false, and everything else is true. the same
--is not true in JS, so we have to think about how to handle gammaPlus
--and gammaMinus with VPIds.

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
  --function taken from TS. TODO: make sure is fine.
  "function"  -> VPType (TFunc [TUnion []] Nothing (TId "any") LPNone) x
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

refined (TRefined main ref) = ref
refined t = t  
