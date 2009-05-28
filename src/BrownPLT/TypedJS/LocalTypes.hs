module BrownPLT.TypedJS.LocalTypes 
  ( localTypes
  ) where

import TypedJavaScript.Types
import BrownPLT.TypedJS.Prelude
import BrownPLT.JavaScript.Analysis.ANF
import qualified BrownPLT.JavaScript.Analysis.LocalTypes as LT
import qualified Data.Map as M
import qualified Data.Set as S
import BrownPLT.JavaScript.Analysis.Intraprocedural (Graph)


localTypes :: Graph
           -> Env -- ^enclosing environment
           -> Map Id Type
           -> Map Node Env -- ^environment at each statement
localTypes gr env typeAliases = staticEnvs
  where f (id, Nothing) = Just (id, LT.TUnreachable)
        f (id, Just (tDec, _, _, _)) = Just (id, asRuntimeType typeAliases tDec)
        -- visible, runtime types of the initial environment
        decEnv = M.fromList $ mapMaybe f (M.toList env)
        
        -- visible, runtime types at each statement
        visibleEnvs = LT.localTypes gr decEnv
        
        toStatic id rt = case M.lookup id  env of
          Nothing -> error "TypedJS.LocalTypes: unbound id"
          Just Nothing -> Nothing
          Just (Just (tDec, tAct, False, vp)) -> Just (tDec, tAct, False, vp)
          Just (Just (t, _, True, vp)) -> 
            Just (t, asStaticType typeAliases rt t, True, vp)
        -- visible, static environments at each statement
        staticEnvs = M.map (\env -> M.mapWithKey toStatic env) visibleEnvs
        


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
  TApp _ _ -> error $ "asRuntimeType aliases: unxpected TApp"
  TForall _ _ t' ->  asRuntimeType aliases t'
  TEnvId id -> case M.lookup id aliases of
    Just t' -> asRuntimeType aliases t'
    Nothing -> error $ printf "asRuntimeType: unbound (TEnvId %s)" id
  TIterator {} -> error "asRuntimeType aliases: TIterator NYI"
  TProperty {} -> error "asRuntimeType aliases: TProperty NYI"
  TPrototype {} -> error "asRuntimeType aliases: TPrototype NYI"
  TUnion ts -> case map (asRuntimeType aliases) ts of
    [] -> error "asRuntimeType aliases: empty union"
    [rt] -> rt
    (rt:rts) -> (foldr LT.unionType rt rts)


maybeAsStaticType :: Map Id Type -> LT.Type -> Type -> Maybe Type
maybeAsStaticType aliases rt st = case (rt, st) of
  (_, TRec _ st') -> maybeAsStaticType aliases rt st'
  (_, TEnvId id) -> case M.lookup id aliases of
    Just (TRec _ (TObject {})) -> case rt of
      LT.TBasic LT.TObject -> Just st
      otherwise -> Nothing
    Just st' -> maybeAsStaticType aliases rt st'
    Nothing -> error $ printf "maybeAsStaticType: unbound (TEnvId %s)" id
  (_, TIterator{}) -> error "maybeAsStaticType aliases: TIterator NYI"
  (_, TPrototype{}) -> error "maybeAsStaticType aliases: TPrototype NYI"
  (_, TProperty{}) -> error "maybeAsStaticType aliases: TProperty NYI"
  (LT.TUnk, st) -> Just st
  
  (LT.TUnion rts, _) -> Just (TUnion (catMaybes sts'))
    where sts' = map (flip (maybeAsStaticType aliases) st) 
                     (map LT.TBasic (S.toList rts))
  (_, TUnion sts) -> Just (TUnion (catMaybes sts'))
    where sts' = map (maybeAsStaticType aliases rt) sts

  (LT.TBasic LT.TString, TId "string") -> Just st
  (LT.TBasic LT.TBoolean, TId "boolean") -> Just st
  (LT.TBasic LT.TNumber, TId "double") -> Just st
  (LT.TBasic LT.TNumber, TId "int") -> Just st
  (LT.TBasic LT.TFunction, TFunc {}) -> Just st
  (LT.TBasic LT.TUndefined, TId "undefined") -> Just st
  (LT.TBasic (LT.TFixedString _), TId "string") -> Just st
  (LT.TBasic LT.TObject, _) -> case st of
    TObject {} -> Just st
    TSequence {} -> Just st
    TApp "Array" _ -> Just st
    otherwise -> Nothing
    
  otherwise -> Nothing -- at runtime if the type is rt, the static type cannot 
                       -- be st

asStaticType aliases rt st = case maybeAsStaticType aliases rt st of
  Just t -> t
  Nothing -> st -- TODO: what?
