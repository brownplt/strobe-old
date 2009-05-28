module BrownPLT.TypedJS.TypeFunctions
  ( globalizeEnv
  , fieldType
  , freeTypeVariables
  , isUnion
  , isObject
  , isSlackObject
  , isAny
  , isConstr
  , isVarRef, isPrototype
  , openObject, closeObject
  , replaceAliases
  , renderLocalEnv
  ) where

import qualified Data.Map as M

import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.TypeDefinitions
import BrownPLT.JavaScript.Analysis.ANF
import TypedJavaScript.PrettyPrint
import TypedJavaScript.Types

--warning: unsound hack for prototypes so that the correct case
--works. constructors keep their refined type so that functions can
--use everything in the prototype.
globalizeEnv :: Env -> Env
globalizeEnv env = M.map f env
  where f (Just (_, t@(TFunc (Just _) _ _ _), _)) = Just (t,t,False)
        f (Just (t1, _, _)) = Just (t1, t1, False)
        f Nothing = Nothing
        

freeTypeVariables :: Type -> Map String Kind
freeTypeVariables t = fv t where
  -- type variables in the constructor are applied
  fv (TApp _ ts) = M.unions (map fv ts)
  fv (TFunc _ args r _) = M.unions (map fv (r:args))
  fv (TSequence args Nothing) = M.unions (map fv args)
  fv (TSequence args (Just opt)) = M.unions (map fv (opt:args))
  fv (TId _) = M.empty
  fv (TObject _ _ props) = M.unions (map (fv.snd) props)
  fv TAny = M.empty
  fv (TRec id t) = M.insert id KindStar (fv t)
  fv (TUnion ts) = M.unions (map fv ts)
  fv (TForall ids _ t) = M.union (M.fromList (zip ids (repeat KindStar)))
                                 (fv t)
fieldType :: Env -> Id -> Type -> Maybe Type
fieldType env id (TObject _ _ ts) = lookup id ts
fieldType env id (TUnion ts) = do
  types <- mapM (fieldType env id) ts
  return (flattenUnion (TUnion types))
fieldType env "length" (TApp "Array" [_]) = return intType
fieldType env "push" (TApp "Array" [t]) = return $ 
  TFunc Nothing [TApp "Array" [t], TSequence [t] Nothing, t] 
        undefType LPNone
--splice and concat are vararg, but ignore that for now.
fieldType env "splice" (TApp "Array" [t]) = return $ 
  TFunc Nothing [TApp "Array" [t], TSequence [TId "int", TId "int"] Nothing, 
                 TId "int", TId "int"] 
        (TApp "Array" [t]) LPNone
fieldType env "concat" (TApp "Array" [t]) = return $ 
  TFunc Nothing [TApp "Array" [t], TSequence [t'] Nothing, t']
        (TApp "Array" [t]) LPNone
    where t' = TUnion [t, TApp "Array" [t]]

--shift really returns U(t, undefined)
fieldType env "shift" (TApp "Array" [t]) = return $ 
  TFunc Nothing [TApp "Array" [t], TSequence [] Nothing] t LPNone
  
fieldType env f (TPrototype c) = case M.lookup c env of
  Just (Just (_, TFunc (Just (TObject _ _ protprops)) _ _ _, _)) ->
    lookup f protprops 
  _ -> Nothing
fieldType _ _ _ = Nothing


isUnion :: Type -> Bool
isUnion (TUnion _) = True
isUnion _ = False

isObject :: Type -> Bool
isObject (TObject _ _ _) = True
isObject _ = False

isConstr :: Type -> Bool
isConstr (TFunc (Just _) _ _ _) = True
isConstr _ = False

isSlackObject :: Type -> Bool
isSlackObject (TObject True _ _) = True
isSlackObject _ = False

isAny :: Type -> Bool
isAny TAny = True
--isAny (TIterator _) = True --these practically act like anyes
--isAny (TProperty _) = True
isAny _ = False

isVarRef (VarRef{}) = True
isVarRef _ = False

isPrototype (TPrototype _) = True
isPrototype _ = False

openObject :: Type -> Type
openObject (TObject hasSlack _ fields) = TObject hasSlack True fields
openObject t = t

closeObject :: Type -> Type
closeObject (TObject hasSlack _ fields) = TObject hasSlack False fields
closeObject t = t

lookupAlias :: KindEnv -> Map String Type -> SourcePos -> Type -> Type
lookupAlias kindEnv tenv pos t = case t of
  TId v -> case M.lookup v kindEnv of
    Just _ -> (TId v)
    Nothing -> case M.lookup v tenv of
      Just t -> t
      Nothing -> (TId v) --real unbound ids will be checked later
  TEnvId v -> case M.lookup v tenv of
    Just t -> t
    Nothing -> TEnvId v
  otherwise -> t


replaceAliases kindEnv tenv p t = everywhere (mkT(lookupAlias kindEnv tenv p)) t

-- |Pretty-prints just the local types in an environment.
renderLocalEnv :: Env -> String
renderLocalEnv env = show (M.map asString (M.filter selectLocal env))
  where selectLocal (Just (_, _, True)) = True
        selectLocal _               = False
        asString (Just (tDec, tAct, _)) = 
          renderType tDec ++ " => " ++ renderType tAct
        asString Nothing = error "renderLocalEnv: expected (Just _)"
