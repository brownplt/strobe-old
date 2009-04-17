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
  , applyType
  , (<:)
  , unionType, unionTypeVP, equalityvp
  , restrict, remove, gammaPlus, gammaMinus
  ) where

--import qualified BrownPLT.JavaScript.Analysis.ANF as ANF
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

--maps names to their type.
--ANF-generated variables have visible predicates.
type Env = Map String (Maybe (Type SourcePos, VP))

emptyEnv :: Env
emptyEnv = M.empty

undefType :: Type SourcePos
undefType = (TId p "undefined")

stringType = TId p "string"

intType = TId p "int"

doubleType = TId p "double"

boolType = TId p "bool"

-- |Deconstructs the declared type of a function, returning a list of quantified
-- variables, the types of each argument, and a return type.  As we enrich the
-- type-checker to handle more of a function type, include them here.
deconstrFnType :: Type SourcePos 
               -> Maybe ([String],[TypeConstraint],[Type SourcePos],Type SourcePos,LatentPred SourcePos)
deconstrFnType (TRefined main refined) = deconstrFnType refined
deconstrFnType t@(TRec id t'@(TFunc{})) = -- Hack to avoid infinite recursion
  deconstrFnType (substType id t t')
deconstrFnType (TFunc _ _ args _ result latentP) = 
  Just ([],[],args,result,latentP)
deconstrFnType (TForall ids constraints (TFunc _ _ args _ result latentP)) = 
  Just (ids,constraints,args,result,latentP)
deconstrFnType _ = Nothing


-- |This is _not_ capture-free.
substType :: String -> Type SourcePos -> Type SourcePos -> Type SourcePos
substType var sub (TRec var' t) 
  | var == var' = error "substType captures"
  | otherwise   = TRec var' (substType var sub t)
substType var sub (TForall formals constraints body)  -- TODO: Subst into?
  | var `elem` formals = TForall formals constraints body
  | otherwise = TForall formals constraints (substType var sub body)
substType var sub (TApp p constr args) = 
  TApp p constr (map (substType var sub) args)
substType var sub (TUnion ts) = 
  TUnion (map (substType var sub) ts)
substType var sub (TId p var')
  | var == var' = sub
  | otherwise =  TId p var'
substType var sub (TFunc p Nothing args vararg ret latentP) =
  TFunc p Nothing (map (substType var sub) args)
        (liftM (substType var sub) vararg)
        (substType var sub ret)
        latentP
substType var sub (TObject p fields) =
  TObject p (map (\(v,t) -> (v,substType var sub t)) fields)
substType _ _ (TFunc _ (Just _) _ _ _ _) = 
  error "cannot substitute into functions with this-types"
substType _ _ (TRefined _ _) = error "substType TRefined NYI"

applyType :: Monad m => Type SourcePos -> [Type SourcePos] -> m (Type SourcePos) -- TODO: ensure constraints
applyType (TForall formals constraints body) actuals = do
  unless (length formals == length actuals) $ do
    fail $ "quantified type has " ++ show (length formals) ++ " variables " ++
           "but " ++ show (length actuals) ++ " were supplied"
  return $ foldr (uncurry substType) body (zip formals actuals)
applyType t [] = return t
applyType t actuals =
  fail $ "type " ++ show t ++ " is not quantified, but " ++ 
         show (length actuals)  ++ " type arguments were supplied"


-- |Infers the type of a literal value.  Used by the parser to parse 'literal
-- expressions in types
inferLit :: Monad m 
         => TJS.Expression SourcePos
         -> m (Type SourcePos)
inferLit (TJS.StringLit p _) = return (TId p "string")
inferLit (TJS.NumLit p _) = return (TId p "double")
inferLit (TJS.IntLit p _) = return (TId p "int")
inferLit (TJS.BoolLit p _) = return (TId p "bool")
inferLit expr =
  fail $ "Cannot use as a literal"

x <: y = x <:~ y
x <:~ y = isSubType' x y


assert :: Bool -> Maybe ()
assert False = Nothing
assert True = Just ()

anyM :: (a -> b -> Maybe a) -> a -> [b] -> Maybe a
anyM _ a [] = Nothing
anyM f a (b:bs) = case f a b of
  Nothing -> anyM f a bs
  Just a  -> return a

-- based on TAPL p.305
st :: Set (Type SourcePos, Type SourcePos)
   -> (Type SourcePos, Type SourcePos)
   -> Maybe (Set (Type SourcePos, Type SourcePos))
st rel (t1, t2)
  | (t1, t2) `S.member` rel = return rel
  | otherwise = case (t1, t2) of
    (TId _ "int", TId _ "double") -> return rel
    (_, TId _ "any") -> return rel
    (TId _ x, TId _ y) 
      | x == y   -> return rel
      | otherwise -> fail $ printf "%s is not a subtype of %s" x y
    (TRefined declared1 refined1, TRefined declared2 refined2) ->
      st (S.insert (t1, t2) rel) (refined1, declared2)
    (TRefined declared refined, other) ->
      st (S.insert (t1, t2) rel) (refined, other)
    (other, TRefined declared refined) -> 
      st (S.insert (t1, t2) rel) (other, declared)
    (TApp _ c1 args1, TApp _ c2 args2) -> do
      assert (length args1 == length args2)
      assert (c1 == c2)
      assert (args1 == args2)
      return rel
      -- rel <- st (S.insert (t1, t2) rel) (c1, c2)
      -- foldM st rel (zip args1 args2) 
    (TFunc _ _ req2 Nothing ret2 lp2, TFunc _ _ req1 Nothing ret1 lp1) -> do
      assert (length req2 == length req1)
      assert (lp1 == lp2 || lp1 == LPNone)
      rel <- st (S.insert (t1, t2) rel) (ret2, ret1)
      foldM st rel (zip req1 req2)
    (TForall ids1 tcs1 t1, TForall ids2 tcs2 t2) -> do
      assert (ids1 == ids2)
      assert (tcs1 == tcs2)
      st (S.insert (t1, t2) rel) (t1, t2)
    (TObject _ props1, TObject _ props2) -> do
      -- All of props2 must be in props1
      let prop rel (id2, t2) = do
            t1 <- lookup id2 props1
            case (t1, t2) of
              (TObject _ _, TObject _ _) -> st rel (t1, t2)
              otherwise -> assert (t1 == t2) >> return rel
      foldM prop (S.insert (t1, t2) rel) props2
    (TUnion ts1, t2) -> do
      foldM (\rel t1 -> st rel (t1, t2)) rel ts1 -- all
    (t1, TUnion ts2) -> do
      anyM (\rel t2 -> st rel (t1, t2)) rel ts2
    (t1, TRec v t2') -> do
      st (S.insert (t1, t2) rel) (t1, substType v t2 t2')
    (TRec v t1', t2) -> do
      st (S.insert (t1, t2) rel) (substType v t1 t1', t2)
    otherwise -> fail $ printf "%s is not a subtype of %s" (show t1) (show t2)
    





isSubType' :: Type SourcePos -> Type SourcePos -> Bool
isSubType' t1 t2 = case st S.empty (t1, t2) of
  Just _ -> True
  Nothing -> False

unionType :: Maybe (Type SourcePos) 
          -> Maybe (Type SourcePos)
          -> Maybe (Type SourcePos)
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

unionTypeVP :: Maybe (Type SourcePos, VP)
            -> Maybe (Type SourcePos, VP)
            -> Maybe (Type SourcePos, VP)
unionTypeVP Nothing Nothing = Nothing
unionTypeVP Nothing (Just (t, v)) = Just (TUnion [undefType, t], VPNone)
unionTypeVP (Just (t, v)) Nothing = Just (TUnion [t, undefType], VPNone)
unionTypeVP (Just (t1, vp1)) (Just (t2, vp2)) = 
  case unionType (Just t1) (Just t2) of
    Nothing -> Nothing
    Just t  -> Just (t, takeEquals vp1 vp2)
flattenUnion :: (Type SourcePos) -> (Type SourcePos)
flattenUnion (TUnion ts) = 
	case (foldl (\res t -> case t of 
                       TUnion tocomb -> res ++ tocomb
                       regular -> res ++ [regular])
                    [] ts) of
          [onet] -> onet
          noneormanyt -> TUnion noneormanyt

flattenUnion  t = t


-- Helpers for occurrence typing, from TypedScheme paper
-- TODO: should occurrence typing have isSubType', or isSubType ?
restrict :: (Type SourcePos) -> (Type SourcePos) -> (Type SourcePos)
restrict (TRefined main ref) t = case restrict ref t of
  TRefined _ reallyrefined -> TRefined main reallyrefined
  reallyrefined -> TRefined main reallyrefined
restrict s t
 | s <:~ t = s
 | otherwise = case t of
     --TODO: make sure TRefined-ness deals well with the following case:
     TUnion ts -> flattenUnion $ 
                        TUnion (map (restrict s) ts)
     --TODO: make sure restrict is correct; this is different than
     --the typed scheme paper
     --TODO: make sure returning a TRefined here is correct
     _ -> let rez = flattenUnion $
                      TUnion (filter (\hm -> isSubType' hm t)
                                     (case s of
                                        TUnion ts -> ts
                                        _ -> [s]))
           in case rez of 
                TUnion [] -> TRefined s t
                _ -> TRefined s rez

remove :: (Type SourcePos) -> (Type SourcePos) -> (Type SourcePos)
remove (TRefined main ref) t = case remove ref t of
  TRefined _ reallyrefined -> TRefined main reallyrefined
  reallyrefined -> TRefined main reallyrefined
remove s t
 | s <:~ t = TUnion  []
 | otherwise = case t of
     TUnion ts -> flattenUnion $ 
                        TUnion (map (remove s) ts)
     --TODO: make sure remove is correct; this is different than
     --the typed scheme paper
     _ -> TRefined s $ flattenUnion $ 
            TUnion  
                   (filter (\hm -> not $ isSubType' hm t)
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
--gammaPlus g (VPId x) = error "Gamma + VPId NYI" 
gammaPlus g (VPNot vp) = gammaMinus g vp
gammaPlus g (VPMulti vs) = foldl gammaPlus g vs
gammaPlus g _ = g

gammaMinus :: Env -> VP -> Env
gammaMinus env (VPType t v) = case M.lookup v env of
  Nothing -> env
  Just Nothing -> env
  Just (Just (t', vp_t)) -> M.insert v (Just (remove t' t, vp_t)) env
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
equalityvp (VPTypeof x) (VPLit (StringLit l s) (TId _ "string")) = case s of
  "number"    -> VPType (TId p "double") x
  "undefined" -> VPType undefType x
  "boolean"   -> VPType (TId p "bool") x
  "string"    -> VPType (TId p "string") x
  "function"  -> error "vp for typeof x == 'function' nyi"
  "object"    -> error "vp for typeof x == 'object' nyi"
  _           -> VPNone
equalityvp a@(VPLit (StringLit l s) (TId _ "string")) b@(VPTypeof x) = 
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
