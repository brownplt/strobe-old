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
areSubTypes _ _ = False


-- |Canonizes types such as int U int to int.
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

-- |Assumes that the components are already canonized.
canonicalUnion :: Type -> Type -> Type
canonicalUnion t1 t2
  | isSubtype t1 t2 = t2
  | isSubtype t2 t1 = t1
  | t1 < t2 = TUnion t1 t2
  | otherwise = TUnion t2 t1


isSubtype :: Type
          -> Type
          -> Bool
isSubtype s t = case (s, t) of
  (_, TAny) ->
    True
  (TApp "Int" [], TApp "Double" []) ->
    True
  (TApp c1 args1, TApp c2 args2) ->
    c1 == c2 && areSubtypes args1 args2
  (TArguments (ArgType args1 optArg1), TArguments (ArgType args2 optArg2)) ->
    areSubtypes args1 args2 -- TODO: arity, blah blah blah
  (TArrow this1 args1 r1, TArrow this2 args2 r2) ->
    isSubtype this2 this1 &&
    isSubtype (TArguments args2) (TArguments args1) &&
    isSubtype r1 r2
  (_, TUnion t1 t2) ->
    isSubtype s t1 || isSubtype s t2
  (TUnion s1 s2, _) -> 
    isSubtype s1 t && isSubtype s2 t
  otherwise -> error $ "isSubtype NYI " ++ show (s, t)


injRT :: RuntimeType -> RuntimeTypeInfo
injRT bt = TKnown (S.singleton bt)


runtime :: Type -> RuntimeTypeInfo
runtime t = case t of
  TAny -> TUnk
  TApp "String" [] ->  injRT RTString
  TApp "Bool" [] ->  injRT RTBoolean
  TApp "Double" [] ->  injRT RTNumber
  TApp "Int" [] ->  injRT RTNumber
  TApp "Undefined" [] ->  injRT RTUndefined
  TArguments _ -> injRT RTObject -- the type of the arguments array
  TArrow _ _ _ -> injRT RTFunction
  TUnion t1 t2 -> case (runtime t1, runtime t2) of
    (TUnk, _) -> TUnk
    (_, TUnk) -> TUnk
    -- cases above should not happen if t is canonized
    (TKnown s1, TKnown s2) -> TKnown (S.union s1 s2)
    (TUnreachable, _) -> error "runtime: recursive call produced TUnreachable"
    (_, TUnreachable) -> error "runtime: recursive call produced TUnreachable"


-- |If the supplied type is canonical, the result is canonical.
static :: Set RuntimeType -> Type -> Maybe Type
static rt st = case st of
  TApp "String" []| S.member RTString rt -> Just st
  TApp "Bool" [] | S.member RTBoolean rt -> Just st
  TApp "Double" [] | S.member RTNumber rt -> Just st
  TApp "Int" [] | S.member RTNumber rt -> Just st
  TApp "Undefined" [] | S.member RTUndefined rt -> Just st
  TArrow _ _ _ | S.member RTFunction rt -> Just st
  TUnion t1 t2 -> case (static rt t1, static rt t2) of
    (Just u1, Just u2) -> Just (canonicalUnion u1 u2)
    (Just u1, Nothing) -> Just u1
    (Nothing, Just u2) -> Just u2
    (Nothing, Nothing) -> Nothing
  otherwise -> Nothing
