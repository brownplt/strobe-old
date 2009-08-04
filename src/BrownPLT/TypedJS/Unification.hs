module BrownPLT.TypedJS.Unification 
  ( unify
  , unifyList
  , subst
  ) where

import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.PrettyPrint (renderType)
import BrownPLT.TypedJS.Infrastructure
import BrownPLT.TypedJS.TypeDefinitions
import qualified Data.Map as M


doesOccurIn :: String
            -> Type
            -> Bool
doesOccurIn x ty = occ ty
  where occField (_, _, ty) = occ ty 
        occArg (ArgType argTys opt) = any occ argTys || maybe False occ opt
        occ ty = case ty of
          TAny -> False
          TObject _ argTys fields -> any occ argTys || any occField fields
          TArrow thisTy args retTy -> occ thisTy || occArg args || occ retTy
          TId y | x == y -> True
                | otherwise -> False
          TIx _ -> False
          TApp _ tys -> any occ tys
          TUnion ty1 ty2 -> occ ty1 || occ ty2
          TExists ty -> occ ty
          TForall ty -> occ ty
          TNamedForall y ty | x == y -> False
                            | otherwise -> occ ty
          TIntersect ty1 ty2 -> occ ty1 || occ ty2
          TConstr argTys initTy retTy ->
            any occ argTys || occ initTy || occ retTy


type Subst = Map String Type


subst :: Subst -> Type -> Type
subst s ty = everywhere (mkT f) ty
  where f :: Type -> Type
        f (TId x) = case M.lookup x s of
          Just ty -> ty
          Nothing -> TId x
        f ty = ty


extendSubst :: Subst -> String -> Type -> Subst
extendSubst s x ty = M.insert x ty (M.map (subst (M.singleton x ty)) s)


unifyAllM :: EnvM m
          => [Type]
          -> [Type]
          -> Subst
          -> m Subst
unifyAllM xs ys s = case (xs, ys) of
  ([], []) -> return s
  (x:xs, y:ys) -> do
    s <- unifyM (subst s x) (subst s y) s
    unifyAllM xs ys s
  otherwise -> fail "unification failed: lists of uneven lengths"


unifyArgsM :: EnvM m
           => ArgType
           -> ArgType
           -> Subst
           -> m Subst
unifyArgsM (ArgType args1 opt1) (ArgType args2 opt2) s = do
  s <- unifyAllM args1 args2 s
  return s


unifyFieldsM :: EnvM m
             => [Field]
             -> [Field]
             -> Subst
             -> m Subst
unifyFieldsM [] [] s = return s
unifyFieldsM _ [] s = return s -- permit extra fields on LHS
unifyFieldsM [] _ s = fail "unification failed on an object"
unifyFieldsM ((f1, ro1, ty1):xs) ((f2, ro2, ty2):ys) s
  | f1 < f2 = unifyFieldsM xs ((f2, ro2, ty2):ys) s -- extra field on LHS
  | f2 > f1 = fail "unification failed: extra field on RHS"
  | otherwise = case (ro1, ro2) of
      (True, False) -> fail "unification failed: field r/w permissions"
      (False, False) -> do
        s <- unifyM (subst s ty1) (subst s ty2) s
        s <- unifyM (subst s ty2) (subst s ty1) s
        unifyFieldsM xs ys s
      (_, True) -> do
        s <- unifyM (subst s ty1) (subst s ty2) s
        unifyFieldsM xs ys s

          
unifyM :: EnvM m
       => Type
       -> Type
       -> Subst
       -> m Subst
unifyM ty1 ty2 s = case (ty1, ty2) of
  (TObject brand1 argTys1 fields1, TObject brand2 argTys2 fields2) -> do
    r <- isSubbrand brand1 brand2
    unless r $ fail $ printf 
      "unification failed: %s is not a sub-brand of %s" brand1 brand2
    s <- unifyAllM argTys1 argTys2 s
    s <- unifyFieldsM fields1 fields2 s
    return s
  (TAny, TAny) -> return s
  (TArguments arg1, TArguments arg2) -> unifyArgsM arg1 arg2 s
  (TArrow thisTy1 args1 retTy1, TArrow thisTy2 args2 retTy2) -> do
    s <- unifyM thisTy2 thisTy1 s
    s <- unifyArgsM args2 args1 s
    unifyM retTy1 retTy2 s
  (TIx x, TIx y) -> do
    unless (x == y) $ fail $ printf
      "unification failed: cannot unify bound variables %s and %s"
      (show x) (show y)
    return s
  (TApp constr1 argTys1, TApp constr2 argTys2) -> do
    unless (constr1 == constr2) $ fail $ printf
      "cannot unify %s with %s" constr1 constr2
    unifyAllM argTys1 argTys2 s
  (TId v1, TId v2) 
    | v1 == v2 -> return s
    | otherwise -> case (v1, v2) of
        ('#':_, _) -> return (extendSubst s v1 (TId v2))
        otherwise -> return (extendSubst s v2 (TId v1))
  (TId v1, ty2) 
    | v1 `doesOccurIn` ty2 -> fail $ printf
        "unification failed: %s occurs in %s" v1 (renderType ty2)
    | otherwise -> return (extendSubst s v1 ty2)
  (ty1, TId v2)
    | v2 `doesOccurIn` ty1 -> fail $ printf
        "unification failed: %s occurs in %s" v2 (renderType ty1)
    | otherwise -> return (extendSubst s v2 ty1)
  (TUnion ty11 ty12, TUnion ty21 ty22) -> do
    s <- unifyM ty11 ty21 s
    unifyM (subst s ty12) (subst s ty22) s
  (TIntersect ty11 ty12, TIntersect ty21 ty22) -> do
    s <- unifyM ty11 ty21 s
    unifyM (subst s ty12) (subst s ty22) s
  (TExists ty1, TExists ty2) -> unifyM ty1 ty2 s
  (TForall ty1, ty2) -> unifyM ty1 ty2 s
  (TNamedForall x ty1, TNamedForall y ty2) ->
    unifyM ty1 (subst (M.singleton y (TId x)) ty2) (extendSubst s y (TId x))
  otherwise -> fail $ printf "unification failed: cannot unify\n%s\nwith\n%s"
    (renderType ty1) (renderType ty2)


unifyList :: EnvM m
          => [Type]
          -> [Type]
          -> m Subst
unifyList tys1 tys2 = unifyAllM tys1 tys2 M.empty


unify :: EnvM m
      => Type
      -> Type
      -> m Subst
unify t1 t2 = do
  unifyM t1 t2 M.empty
