module BrownPLT.TypedJS.TypeTheory
  ( undefType
  , stringType
  , intType
  , doubleType
  , boolType
  , isSubtype
  , canonize
  , runtime
  , static
  , canonicalUnion
  ) where

import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.TypeDefinitions
import qualified Data.Set as S



undefType = TApp "Undefined" []

stringType = TApp "String" []

intType = TApp "Int" []

doubleType = TApp "Double" []

boolType = TApp "Bool" []


areSubtypes :: [Type]
            -> [Type]
            -> Bool
areSubtypes [] [] = True
areSubtypes (s:ss) (t:ts) = isSubtype s t && areSubtypes ss ts
areSubtypes _ _ = False


-- |Canonizes types such as int U int to int.  Orders fields lexicographically.
canonize:: Type -> Type
canonize t = case t of
  TAny -> t
  TApp c args -> TApp c (map canonize args)
  TArguments (ArgType args opt) -> 
    TArguments (ArgType (map canonize args) (liftM canonize opt))
  TArrow this (ArgType args opt) r ->
    TArrow (canonize this) (ArgType (map canonize args) (liftM canonize opt))
           (canonize r)
  TUnion t1 t2 -> canonicalUnion (canonize t1) (canonize t2)
  TObject brand fields -> TObject brand (sortBy cmp (map f fields))
    where f (x, ro, t) = (x, ro, canonize t)
          cmp (x, _, _) (y, _, _) = compare x y
  otherwise -> error $ " canonize NYI " ++ show t

-- |Assumes that the components are already canonized.
canonicalUnion :: Type -> Type -> Type
canonicalUnion t1 t2
  | isSubtype t1 t2 = t2
  | isSubtype t2 t1 = t1
  | t1 < t2 = TUnion t1 t2
  | otherwise = TUnion t2 t1


-- Width and subsumption.  'canonize' handles permutations.
areFieldsSubtypes :: [Field] -> [Field] -> Bool
areFieldsSubtypes _ [] = True
areFieldsSubtypes [] _ = False
areFieldsSubtypes ((x1, ro1, t1):fs1) ((x2, ro2, t2):fs2)
  | x1 < x2 = areFieldsSubtypes fs1 ((x2, ro2, t2):fs2)
  | x1 == x2 = case (ro1, ro2) of
      (_, True) -> isSubtype t1 t2 && areFieldsSubtypes fs1 fs2
      (False, False) -> t1 == t2 && areFieldsSubtypes fs1 fs2
      otherwise -> False
  | otherwise = False


-- |Assumes the arguments are in canonical forms.
isSubtype :: Type
          -> Type
          -> Bool
isSubtype s t = case (s, t) of
  (_, TAny) ->
    True
  (TApp "Int" [], TApp "Double" []) ->
    True
  (TObject brand1 fs1, TObject brand2 fs2) -> -- TODO: support brands
    areFieldsSubtypes fs1 fs2
  (TApp c1 args1, TApp c2 args2) ->
    c1 == c2 && areSubtypes args1 args2
  (TArguments (ArgType args1 optArg1), TArguments (ArgType args2 optArg2)) ->
    areSubtypes args1 args2 -- TODO: arity, blah blah blah
  (TArrow this1 args1 r1, TArrow this2 args2 r2) ->
    isSubtype this2 this1 &&
    isSubtype (TArguments args2) (TArguments args1) &&
    isSubtype r1 r2
  (TUnion s1 s2, _) -> 
    isSubtype s1 t && isSubtype s2 t
  (_, TUnion t1 t2) ->
    isSubtype s t1 || isSubtype s t2
  otherwise -> False


injRT :: RuntimeType -> RuntimeTypeInfo
injRT bt = TKnown (S.singleton bt)


runtime :: Type -> RuntimeTypeInfo
runtime t = case t of
  TId x -> error $ printf "TypeTheory.hs : argument of runtime contains \
                          \free type variable %s" x
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
static :: Set RuntimeType -> Type -> Maybe Type
static rt st = case st of
  TAny -> case map flatStatic (S.toList rt) of
    [] -> Nothing
    [t] -> Just t
    (t:ts) -> Just (foldr canonicalUnion t ts)
  TApp "String" [] | S.member RTString rt -> Just st
  TApp "Bool" [] | S.member RTBoolean rt -> Just st
  TApp "Double" [] | S.member RTNumber rt -> Just st
  TApp "Int" [] | S.member RTNumber rt -> Just st
  TApp "Undefined" [] | S.member RTUndefined rt -> Just st
  TObject _ _ | S.member RTObject rt -> Just st
  TArrow _ _ _ | S.member RTFunction rt -> Just st
  TUnion t1 t2 -> case (static rt t1, static rt t2) of
    (Just u1, Just u2) -> Just (canonicalUnion u1 u2)
    (Just u1, Nothing) -> Just u1
    (Nothing, Just u2) -> Just u2
    (Nothing, Nothing) -> Nothing
  otherwise -> Nothing
