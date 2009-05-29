module BrownPLT.TypedJS.LocalTypes 
  ( localTypes
  , refineEnvWithRuntime
  ) where

import TypedJavaScript.Types
import TypedJavaScript.PrettyPrint
import BrownPLT.TypedJS.Prelude
import BrownPLT.JavaScript.Analysis.ANF
import qualified BrownPLT.JavaScript.Analysis.LocalTypes as LT
import qualified Data.Map as M
import qualified Data.Set as S
import BrownPLT.JavaScript.Analysis.Intraprocedural (Graph)
import BrownPLT.TypedJS.TypeFunctions


localTypes :: Graph
           -> Env -- ^enclosing environment
           -> Map Id Type
           -> Map Node (Map Id LT.Type) -- ^runtime env. at each statement
localTypes gr env typeAliases =  visibleEnvs
  where f (id, Nothing) = Just (id, LT.TUnreachable)
        f (id, Just (tDec, _, _)) = Just (id, asRuntimeType typeAliases tDec)
        -- visible, runtime types of the initial environment
        decEnv = M.fromList $ mapMaybe f (M.toList env)
        
        -- visible, runtime types at each statement
        visibleEnvs = LT.localTypes gr decEnv


refineEnvWithRuntime :: Map Id Type -> Env -> Map Id LT.Type -> Env
refineEnvWithRuntime typeAliases env rt = env'
  where toStatic id rt = case M.lookup id  env of
          Nothing -> error $ printf "TypedJS.LocalTypes: %s is unbound" id
          Just Nothing -> Nothing
          Just (Just (tDec, t, isLocal)) -> Just (tDec, tAct, isLocal)
            where tAct = asStaticType typeAliases rt (flattenUnion t)
        env' = M.mapWithKey toStatic rt


injBaseType :: LT.BaseType -> LT.Type
injBaseType bt = LT.TKnown (S.singleton bt)


projBaseType :: LT.Type -> Maybe LT.BaseType
projBaseType (LT.TKnown set) = case S.toList set of
  [t] -> Just t
  otherwise -> Nothing
projBaseType _ = Nothing


projUnionType  :: LT.Type -> Maybe [LT.Type]
projUnionType (LT.TKnown set) = case S.toList set of
  ts@(_:_:_) -> Just (map (\t -> LT.TKnown (S.singleton t)) ts)
  otherwise -> Nothing
projUnionType _ = Nothing


asRuntimeType :: Map Id Type -> Type -> LT.Type
asRuntimeType aliases t = case t of
  TObject {} ->  injBaseType LT.TObject
  TAny ->  LT.TUnk
  TRec _ _ ->  asRuntimeType aliases (unRec t)
  TSequence _ _ ->  injBaseType LT.TObject
  TFunc {} ->  injBaseType LT.TFunction
  TId "string" ->  injBaseType LT.TString
  TId "bool" ->  injBaseType LT.TBoolean
  TId "double" ->  injBaseType LT.TNumber
  TId "int" ->  injBaseType LT.TNumber
  TId "undefined" ->  injBaseType LT.TUndefined
  --TId s -> error $ printf "asRuntimeType aliases: unexpected (TId %s)" s
  TId s -> LT.TUnk --a parametrized type (like in a forall)
  TApp "Array" _ ->  injBaseType LT.TObject
  TPrototype {} ->  injBaseType LT.TObject
  TApp _ _ -> error $ "asRuntimeType aliases: unxpected TApp"
  TForall _ _ t' ->  asRuntimeType aliases t'
  TEnvId id -> case M.lookup id aliases of
    Just t' -> asRuntimeType aliases t'
    Nothing -> error $ printf "asRuntimeType: unbound (TEnvId %s)" id
  TIterator {} -> error "asRuntimeType aliases: TIterator NYI"
  TProperty {} -> error "asRuntimeType aliases: TProperty NYI"
  TUnion ts -> case map (asRuntimeType aliases) ts of
    [] -> error "asRuntimeType aliases: empty union"
    [rt] -> rt
    (rt:rts) -> let x = (foldr LT.unionType rt rts) in x

maybeAsStaticType :: Map Id Type -> LT.Type -> Type -> Maybe Type
maybeAsStaticType aliases rt st = case (rt, st) of
  (_, TRec id st') -> do
    t <- maybeAsStaticType (M.insert id (TId id) aliases) rt st'
    return (TRec id t)
  (_, TForall ids constraints type_) -> do
    let ids' = M.fromList $ map (\id -> (id, TId id)) ids
    type_' <- maybeAsStaticType (M.union ids' aliases) rt type_
    return (TForall ids constraints type_') 
  (_, TEnvId id) -> case M.lookup id aliases of
    Just (TRec _ (TObject {})) -> case rt of
      (projBaseType -> Just LT.TObject) -> Just st
      otherwise -> Nothing
    Just (TObject {}) -> case rt of
      (projBaseType -> Just LT.TObject) -> Just st
      otherwise -> Nothing
    Just st' -> maybeAsStaticType aliases rt st'
    Nothing -> error $ printf "maybeAsStaticType: unbound (TEnvId %s)" id
  (LT.TUnk, st) -> Just st
  
  (_, TId id) | id `M.member` aliases -> Just (TId id)
  (projBaseType -> Just LT.TString, TId "string") -> Just st
  (projBaseType -> Just LT.TBoolean, TId "bool") -> Just st
  (projBaseType -> Just LT.TNumber, TId "double") -> Just st
  (projBaseType -> Just LT.TNumber, TId "int") -> Just st
  (projBaseType -> Just LT.TFunction, TFunc {}) -> Just st
  (projBaseType -> Just LT.TUndefined, TId "undefined") -> Just st
  (projBaseType -> Just (LT.TFixedString _), TId "string") -> Just st
  (projBaseType -> Just LT.TObject, _) -> case st of
    TObject {} -> Just st
    TSequence {} -> Just st
    TApp "Array" _ -> Just st
    TPrototype {} -> Just st --TODO: i think...
    otherwise -> Nothing
  (projUnionType -> Just rts, TUnion sts) -> do
    let projs = [maybeAsStaticType aliases rt st | rt <- rts, st <- sts]
    case catMaybes projs of
      [] -> Nothing
      [t] -> Just t
      ts -> Just (TUnion ts)
  

  (_, TIterator{}) -> error "maybeAsStaticType aliases: TIterator NYI"
  (_, TPrototype{}) -> Just st
  (_, TProperty{}) -> error "maybeAsStaticType aliases: TProperty NYI"
  
  (projUnionType -> Just rts, _) -> 
    case catMaybes (map (flip (maybeAsStaticType aliases) st) rts) of
      [] -> Nothing
      [t] -> Just t
      ts -> Just (TUnion ts)
  (_, TUnion sts) -> 
    case catMaybes $ map (maybeAsStaticType aliases rt) sts of
      [] -> Nothing
      [t] -> Just t
      ts -> Just (TUnion ts)
    
  otherwise -> Nothing -- at runtime if the type is rt, the static type cannot 
                       -- be st

asStaticType aliases rt st = case maybeAsStaticType aliases rt st of
  Just t -> t
  Nothing -> st -- TODO: what?
