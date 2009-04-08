module TypedJavaScript.Types 
  ( Env
  , emptyEnv
 -- , argEnv
  , undefType
  , stringType
  , intType
  , doubleType
  , boolType
  , inferLit
  , unTVal
  , deconstrFnType
  , applyType
  , freeTIds
  , (<:)
  , unionType, unionTypeVP
  ) where

import qualified BrownPLT.JavaScript.Analysis.ANF as ANF
import TypedJavaScript.Prelude
import TypedJavaScript.PrettyPrint()
import TypedJavaScript.Syntax
import qualified Data.Set as S
import qualified Data.Map as M

import TypedJavaScript.Syntax (Type (..))

p = initialPos "TypedJavaScript.Types"

--maps names to their type.
--ANF-generated variables have visible predicates.
type Env = Map String (Maybe (Type SourcePos, Maybe VP))

emptyEnv :: Env
emptyEnv = M.empty

undefType :: Type SourcePos
undefType = (TId p "undefined")

stringType = TId p "string"

intType = TId p "int"

doubleType = TId p "double"

boolType = TId p "bool"

{-
-- |Builds the local enviroment of a function.
argEnv :: [(String,Type SourcePos)] -- ^positional arguments
       -> Maybe (String,Type SourcePos) -- ^vararity argument
       -> Env
argEnv posArgs varArg = addVarArg $ foldl' addPosArg emptyEnv posArgs where
  addPosArg env (x,t) = M.insertWith'
    (error $ "repeated identifier " ++ x ++ " in an argument list")
    x t env
  addVarArg env = case varArg of
    Nothing -> env
    Just (x,t) -> M.insertWith'
      (error $ "repeated identifier " ++ x ++ " in an argument list")
      x t env
-}
-- |Deconstructs the declared type of a function, returning a list of quantified
-- variables, the types of each argument, and a return type.  As we enrich the
-- type-checker to handle more of a function type, include them here.
deconstrFnType :: Type SourcePos 
               -> Maybe ([String],[TypeConstraint],[Type SourcePos],Type SourcePos,LatentPred SourcePos)
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
substType var sub (TVal e t) = 
  TVal e t -- should not need to subst
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

freeTIds :: Type SourcePos -> S.Set String
freeTIds type_ = 
  everythingBut S.union (mkQ True isNotForall) (mkQ S.empty findTId) type_ where
    isNotForall :: Type SourcePos -> Bool
    isNotForall (TForall _ _ _) = False
    isNotForall _ = True
 
    findTId :: Type SourcePos -> S.Set String
    findTId (TId _ v) = S.singleton v
    findTId (TForall vars _ t) = S.difference (freeTIds t) (S.fromList vars)
    findTId _ = S.empty
  


-- |Infers the type of a literal value.  Used by the parser to parse 'literal
-- expressions in types
inferLit :: Monad m 
         => Expression SourcePos
         -> m (Type SourcePos)
inferLit (StringLit p _) = return (TId p "string")
inferLit (NumLit p _) = return (TId p "double")
inferLit (IntLit p _) = return (TId p "int")
inferLit (BoolLit p _) = return (TId p "bool")
inferLit expr =
  fail $ "Cannot use as a literal"

unTVal (TVal _ t) = t
unTVal t = error $ "unTVal expected a TVal, received " ++ show t

x <: y = x <:~ y
x <:~ y = isSubType' x y

isSubType' :: Type SourcePos -> Type SourcePos -> Bool
--objects are invariant in their common field types
--TODO: verify that the 'case' here is well-founded, and that I'm not
--      doing something silly.
isSubType' (TObject _ props1) (TObject _ props2) =
  all (\(o2id@(Id _ o2propname), o2proptype) -> maybe
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

--the first of these cases works if both are unions; the second does not.
{- 
(x U y) <: (x U y)
--------------------------
first: x <: x U y and y <: x U y
-----------------------------------------
second: 
(x U y) <: x or (x U y) <: y
(x <: x and x <: y) or (x <: y and y <: y)
-}
isSubType' (TUnion _ ts) t = case ts of
  [] -> False
  _ -> all (\ti -> ti <:~ t) ts
isSubType' t (TUnion _ ts) = any (t <:~) ts
isSubType' _ (TId _ "any") = True -- TODO: O RLY?
isSubType' (TId _ "int") (TId _ "double") = True
isSubType' (TId _ x) (TId _ y) = x == y
isSubType' (TApp _ (TId _ "Array") args1) (TApp _ (TId _ "Array") args2) =
  args1 == args2
isSubType' (TApp _ c1 args1) (TApp _ c2 args2) = 
  c2 <:~ c1 &&
  (and $ zipWith (==) args1 args2) && --TODO: invariance better than subtyping?
  (length args1 == length args2)
isSubType'(TVal v1 t1) (TVal v2 t2) = v1 `eqLit` v2 && t1 <:~ t2
isSubType' (TVal _ t1) t2 = t1 <:~ t2
isSubType' (TForall ids1 tcs1 t1) (TForall ids2 tcs2 t2) = 
  ids1 == ids2 && tcs1 == tcs2 && t1 == t2

isSubType' (TIndex (TObject _ props1) (TVal (ANF.StringLit p s1) _) kn1)
          (TIndex (TObject _ props2) (TVal (ANF.StringLit _ s2) _) kn2) = 
  s1 == s2 && kn1 == kn2 && (do
    p1 <- lookup (Id p s1) props1
    p2 <- lookup (Id p s2) props2
    if p1 <:~ p2
      then return True
      else Nothing) /= Nothing
isSubType' (TIndex o1@(TObject _ props1) kt1@(TUnion _ s1s) kn1)
          (TIndex o2@(TObject _ props2) kt2@(TUnion _ s2s) kn2) = 
  kt1 == kt2 && kn1 == kn2 && 
    all (\s1 -> isSubType' (TIndex o1 s1 kn1) (TIndex o2 s1 kn2))
        s1s

isSubType' _ _ = False


unionType :: Maybe (Type SourcePos) 
          -> Maybe (Type SourcePos)
          -> Maybe (Type SourcePos)
unionType Nothing _ = Nothing
unionType _ Nothing = Nothing
unionType (Just t1) (Just t2)
  | t1 <: t2 = Just t2
  | t2 <: t1 = Just t1
  | otherwise = Just (TUnion noPos [t1, t2]) -- TODO: What?

{- so far, the only things that have VPs are ANF vars,
   and they will never appear in both branches, or after the branch
   they are in at all, so it is irrelevant to keep ther VPs around -}
unionTypeVP :: Maybe (Type SourcePos, Maybe VP)
            -> Maybe (Type SourcePos, Maybe VP)
            -> Maybe (Type SourcePos, Maybe VP)
unionTypeVP Nothing _ = Nothing
unionTypeVP _ Nothing = Nothing
unionTypeVP (Just (t1, mvp1)) (Just (t2, mvp2)) = 
  case unionType (Just t1) (Just t2) of
    Nothing -> Nothing
    Just t  -> Just (t, if mvp1 == mvp2 then mvp1 else Just VPNone)

