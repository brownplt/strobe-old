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
  TypeConstraint(..), LatentPred(..), typePos)
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
deconstrFnType (TFunc _ _ args _ result latentP) = 
  Just ([],[],args,result,latentP)
deconstrFnType (TForall ids constraints (TFunc _ _ args _ result latentP)) = 
  Just (ids,constraints,args,result,latentP)
deconstrFnType _ = Nothing


-- |This is _not_ capture-free.
substType :: String -> Type SourcePos -> Type SourcePos -> Type SourcePos
substType var sub (TForall formals constraints body)  -- TODO: Subst into?
  | var `elem` formals = TForall formals constraints body
  | otherwise = TForall formals constraints (substType var sub body)
substType var sub (TApp p constr args) = 
  TApp p constr (map (substType var sub) args)
substType var sub (TUnion p ts) = 
  TUnion p (map (substType var sub) ts)
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

-- based on TAPL p.305
st :: Set (Type SourcePos, Type SourcePos)
   -> (Type SourcePos, Type SourcePos)
   -> Maybe (Set (Type SourcePos, Type SourcePos))
st rel (t1, t2) = case (t1, t2) of
  (TId _ x, TId _ y) 
    | x == y   -> return rel
    | otherwise -> fail $ printf "%s is not a subtype of %s" x y
  (TId _ "int", TId _ "double") -> return rel
  (_, TId _ "any") -> return rel
  (TRefined declared1 refined1, TRefined declared2 refined2) ->
    st (S.insert (t1, t2) rel) (refined1, declared2)
  (TRefined declared refined, other) ->
    st (S.insert (t1, t2) rel) (refined, other)
  (other, TRefined declared refined) -> 
    st (S.insert (t1, t2) rel) (other, declared)
  (TApp _ c1 args1, TApp _ c2 args2) | length args1 == length args2 -> do
    rel <- st (S.insert (t1, t2) rel) (c1, c2)
    foldM st rel (zip args1 args2) 
  
    
    
  



    

isSubType' :: Type SourcePos -> Type SourcePos -> Bool
--objects are invariant in their common field types
--TODO: verify that the 'case' here is well-founded, and that I'm not
--      doing something silly.
isSubType' (TRefined m1 r1) (TRefined m2 r2) = isSubType' r1 m2
isSubType' (TRefined m r) b = isSubType' r b
isSubType' a (TRefined m r) = isSubType' a m
isSubType' (TObject _ props1) (TObject _ props2) =
  all (\(o2id, o2proptype) -> maybe
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
isSubType' (TUnion _ ts) t = all (\ti -> ti <:~ t) ts
isSubType' t (TUnion _ ts) = any (t <:~) ts
isSubType' _ (TId _ "any") = True -- TODO: O RLY?
isSubType' (TId _ "int") (TId _ "double") = True
isSubType' (TId _ x) (TId _ y) = x == y
isSubType' (TApp _ c1 args1) (TApp _ c2 args2) = 
  c2 <:~ c1 &&
  (and $ zipWith (==) args1 args2) && --TODO: invariance better than subtyping?
  (length args1 == length args2)
isSubType' (TForall ids1 tcs1 t1) (TForall ids2 tcs2 t2) = 
  ids1 == ids2 && tcs1 == tcs2 && t1 == t2

--TODO: check these TRefined stuff
-- the 2nd one can only be a TRefined if we're assigning to it (right?)
-- in this case, we can over-write its refined type, so only the main
-- matters.
isSubType' _ _ = False

{-
-- can you assign a to b? this is just subtyping.
assignable (TRefined m1 r1) (TRefined m2 r2) = isSubType' r1 m2
assignable (TRefined main ref) b = isSubType' ref b
assignable a (TRefined main ref) = isSubType' a main
assignable a b = isSubType' a b -}


unionType :: Maybe (Type SourcePos) 
          -> Maybe (Type SourcePos)
          -> Maybe (Type SourcePos)
unionType Nothing Nothing = error "unionType called with 2 Nothings"
unionType Nothing (Just t) = Just $ TUnion noPos [undefType, t]
unionType (Just t) Nothing = Just $ TUnion noPos [t, undefType]
unionType (Just t1) (Just t2)
  | t1 <: t2 = Just t2
  | t2 <: t1 = Just t1
  | otherwise = Just (TUnion noPos [t1, t2]) -- TODO: What?

-- keep the VPs that are the same
-- TODO: something like VPLit 3 "int", VPLit 4 "int" might be salvageable.
-- TODO: rename this function
takeEquals :: VP -> VP -> VP
takeEquals (VPMulti v1s) (VPMulti v2s) = VPMulti (zipWith takeEquals v1s v2s)
takeEquals (VPMulti v1s) v2 = VPMulti (map (takeEquals v2) v1s)
takeEquals v1 (VPMulti v2s) = VPMulti (map (takeEquals v1) v2s)
takeEquals (VPType t1 id1) (VPType t2 id2) = 
  if id1 == id2 then (VPType (TUnion noPos [t1, t2]) id1) else VPNone
takeEquals v1 v2 = if v1 == v2 then v1 else VPNone

unionTypeVP :: Maybe (Type SourcePos, VP)
            -> Maybe (Type SourcePos, VP)
            -> Maybe (Type SourcePos, VP)
unionTypeVP Nothing Nothing = Nothing
unionTypeVP Nothing (Just (t, v)) = Just (TUnion noPos [undefType, t], VPNone)
unionTypeVP (Just (t, v)) Nothing = Just (TUnion noPos [t, undefType], VPNone)
unionTypeVP (Just (t1, vp1)) (Just (t2, vp2)) = 
  case unionType (Just t1) (Just t2) of
    Nothing -> Nothing
    Just t  -> Just (t, takeEquals vp1 vp2)
flattenUnion :: (Type SourcePos) -> (Type SourcePos)
flattenUnion (TUnion pos ts) = 
	case (foldl (\res t -> case t of 
                       TUnion _ tocomb -> res ++ tocomb
                       regular -> res ++ [regular])
                    [] ts) of
          [onet] -> onet
          noneormanyt -> TUnion pos noneormanyt

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
     TUnion pos ts -> flattenUnion $ 
                        TUnion pos (map (restrict s) ts)
     --TODO: make sure restrict is correct; this is different than
     --the typed scheme paper
     --TODO: make sure returning a TRefined here is correct
     _ -> let rez = flattenUnion $
                      TUnion (typePos s) 
                             (filter (\hm -> isSubType' hm t)
                                     (case s of
                                        TUnion _ ts -> ts
                                        _ -> [s]))
           in case rez of 
                TUnion _ [] -> TRefined s t
                _ -> TRefined s rez

remove :: (Type SourcePos) -> (Type SourcePos) -> (Type SourcePos)
remove (TRefined main ref) t = case remove ref t of
  TRefined _ reallyrefined -> TRefined main reallyrefined
  reallyrefined -> TRefined main reallyrefined
remove s t
 | s <:~ t = TUnion (typePos s) []
 | otherwise = case t of
     TUnion pos ts -> flattenUnion $ 
                        TUnion pos (map (remove s) ts)
     --TODO: make sure remove is correct; this is different than
     --the typed scheme paper
     _ -> TRefined s $ flattenUnion $ 
            TUnion (typePos s) 
                   (filter (\hm -> not $ isSubType' hm t)
                           (case s of
                             TUnion _ ts -> ts
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

-- TODO: combpred is not applicable to us anymore, since we don't
-- have any if expression. this is good/bad?  
combpred :: VP -> VP -> 
            VP -> VP 
combpred (VPType t x1) (VPLit l _) (VPType s x2) 
  | asBool l = if (x1 == x2) 
      then VPType (TUnion (typePos t) [t, s]) x1 --flattenUnion here?
      else VPNone
  | otherwise = VPNone
combpred (VPLit l t) f1 f2 
  | asBool l = f1
  | otherwise = f2
combpred f (VPLit l1 t1) (VPLit l2 t2)
  | (asBool l1) && (not $ asBool l2) = f
  | otherwise = VPNone
combpred f1 f2 f3 = if f2 == f3 then f2 else VPNone

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
