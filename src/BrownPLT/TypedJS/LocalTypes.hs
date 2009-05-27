module BrownPLT.TypedJS.LocalTypes 
  ( localTypes
  ) where

import TypedJavaScript.Types
import BrownPLT.TypedJS.Prelude
import BrownPLT.JavaScript.Analysis.ANF
import qualified BrownPLT.JavaScript.Analysis.LocalTypes as LT
import qualified Data.Map as M
import BrownPLT.JavaScript.Analysis.Intraprocedural (Graph)

localTypes :: Graph
           -> Env -- ^enclosing environment
           -> Map Node Env -- ^environment at each statement
localTypes gr env = staticEnvs
  where f (id, Nothing) = Just (id, LT.TUnk)
        f (id, Just (tDec, _, _, _)) = Just (id, asRuntimeType tDec)
        -- visible, runtime types of the initial environment
        decEnv = M.fromList $ mapMaybe f (M.toList env)
        
        -- visible, runtime types at each statement
        visibleEnvs = LT.localTypes gr decEnv
        
        toStatic id rt = case M.lookup id  env of
          Nothing -> error "TypedJS.LocalTypes: unbound id"
          Just Nothing -> Nothing
          Just (Just (tDec, tAct, False, vp)) -> Just (tDec, tAct, False, vp)
          Just (Just (t, _, True, vp)) -> Just (t, asStaticType rt t, True, vp)
        -- visible, static environments at each statement
        staticEnvs = M.map (\env -> M.mapWithKey toStatic env) visibleEnvs
        


asRuntimeType :: Type -> LT.Type
asRuntimeType t = case t of
  TObject {} ->  LT.TBasic LT.TObject
  TAny ->  LT.TUnk
  TRec _ _ ->  asRuntimeType (unRec t)
  TSequence _ _ ->  LT.TBasic LT.TObject
  TFunc {} ->  LT.TBasic LT.TFunction
  TId "string" ->  LT.TBasic LT.TString
  TId "bool" ->  LT.TBasic LT.TBoolean
  TId "double" ->  LT.TBasic LT.TNumber
  TId "int" ->  LT.TBasic LT.TNumber
  TId "undefined" ->  LT.TBasic LT.TUndefined
  TId s -> error $ printf "asRuntimeType: unexpected (TId %s)" s
  TApp "Array" _ ->  LT.TBasic LT.TObject
  TApp _ _ -> error $ "asRuntimeType: unxpected TApp"
  TForall _ _ t' ->  asRuntimeType t'
  TEnvId s -> error $ printf "asRuntimeType: unexpected (TEnvId %s)" s
  TIterator {} -> error "asRuntimeType: TIterator NYI"
  TProperty {} -> error "asRuntimeType: TProperty NYI"
  TPrototype {} -> error "asRuntimeType: TPrototype NYI"
  TUnion ts -> case map asRuntimeType ts of
    [] -> error "asRuntimeType: empty union"
    [rt] -> rt
    (rt:rts) -> (foldr LT.unionType rt rts)


maybeAsStaticType :: LT.Type -> Type -> Maybe Type
maybeAsStaticType rt st = case (rt, st) of
  (_, TRec _ st') -> maybeAsStaticType rt st'
  (_, TEnvId _) -> error "maybeAsStaticType: TEnvId"
  (_, TIterator{}) -> error "maybeAsStaticType: TIterator NYI"
  (_, TPrototype{}) -> error "maybeAsStaticType: TPrototype NYI"
  (_, TProperty{}) -> error "maybeAsStaticType: TProperty NYI"
  (LT.TUnk, _) -> Just st
  
  (LT.TUnion rts, _) -> Just (TUnion (catMaybes sts'))
    where sts' = map (flip maybeAsStaticType st) (map LT.TBasic rts)
  (_, TUnion sts) -> Just (TUnion (catMaybes sts'))
    where sts' = map (maybeAsStaticType rt) sts

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

asStaticType rt st = case maybeAsStaticType rt st of
  Just t -> t
  Nothing -> st -- TODO: what?
