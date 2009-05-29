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
          Just Nothing -> trace ("dropping: " ++ id) Nothing
          Just (Just (tDec, t, isLocal)) -> Just (tDec, tAct, isLocal)
            where tAct = asStaticType typeAliases rt (flattenUnion t)
                  pr = case isUnion t && not (isUnion tAct) of 
                         False -> ""
                         True -> printf "%s : %s => %s (actually %s)" id (renderType t) (renderType tAct) (show rt)
        -- visible, static environments at each statement

        env' = M.mapWithKey toStatic rt


asRuntimeType :: Map Id Type -> Type -> LT.Type
asRuntimeType aliases t = case t of
  TObject {} ->  LT.TBasic LT.TObject
  TAny ->  LT.TUnk
  TRec _ _ ->  asRuntimeType aliases (unRec t)
  TSequence _ _ ->  LT.TBasic LT.TObject
  TFunc {} ->  LT.TBasic LT.TFunction
  TId "string" ->  LT.TBasic LT.TString
  TId "bool" ->  LT.TBasic LT.TBoolean
  TId "double" ->  LT.TBasic LT.TNumber
  TId "int" ->  LT.TBasic LT.TNumber
  TId "undefined" ->  LT.TBasic LT.TUndefined
  TId s -> error $ printf "asRuntimeType aliases: unexpected (TId %s)" s
  TApp "Array" _ ->  LT.TBasic LT.TObject
  TPrototype {} -> LT.TBasic LT.TObject
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
  (_, TEnvId id) -> case M.lookup id aliases of
    Just (TRec _ (TObject {})) -> case rt of
      LT.TBasic LT.TObject -> Just st
      otherwise -> Nothing
    Just st' -> maybeAsStaticType aliases rt st'
    Nothing -> error $ printf "maybeAsStaticType: unbound (TEnvId %s)" id
  (LT.TUnk, st) -> Just st
  
  (LT.TUnion rts, _) -> 
    case catMaybes (map (flip (maybeAsStaticType aliases) st)
                         (map LT.TBasic (S.toList rts))) of
      [] -> Nothing
      [t] -> Just t
      ts -> Just (TUnion ts)
  (_, TUnion sts) ->
    case catMaybes $ map (maybeAsStaticType aliases rt) sts of
      [] -> Nothing
      [t] -> Just t
      ts -> Just (TUnion ts)
  (_, TId id) | id `M.member` aliases -> Just (TId id)
  (LT.TBasic LT.TString, TId "string") -> Just st
  (LT.TBasic LT.TBoolean, TId "bool") -> Just st
  (LT.TBasic LT.TNumber, TId "double") -> Just st
  (LT.TBasic LT.TNumber, TId "int") -> Just st
  (LT.TBasic LT.TFunction, TFunc {}) -> Just st
  (LT.TBasic LT.TUndefined, TId "undefined") -> Just st
  (LT.TBasic (LT.TFixedString _), TId "string") -> Just st
  (LT.TBasic LT.TObject, _) -> case st of
    TObject {} -> Just st
    TPrototype {} -> Just st --TODO: i think...
    TSequence {} -> Just st
    TApp "Array" _ -> Just st
    otherwise -> Nothing

  --here we have a prototype refined to a non-object. 
  --I think the declared type is always right, though...
  (_, TPrototype{}) -> Just st

  (_, TIterator{}) -> error "maybeAsStaticType aliases: TIterator NYI"
  (_, TProperty{}) -> error "maybeAsStaticType aliases: TProperty NYI"
    
  otherwise -> Nothing -- at runtime if the type is rt, the static type cannot 
                       -- be st

asStaticType aliases rt st = case maybeAsStaticType aliases rt st of
  Just t -> t
  Nothing -> st -- TODO: what?
