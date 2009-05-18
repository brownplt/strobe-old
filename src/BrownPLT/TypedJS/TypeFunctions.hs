module BrownPLT.TypedJS.TypeFunctions
  ( globalizeEnv
  , freeTypeVariables
  , isUnion
  , isObject
  ) where

import qualified Data.Map as M

import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.TypeDefinitions

import TypedJavaScript.Types

globalizeEnv :: Env -> Env
globalizeEnv env = M.map f env
  where f (Just (t1, _, _, vp)) = Just (t1, t1, False, vp)
        f Nothing = Nothing
        

freeTypeVariables :: Type -> Map String Kind
freeTypeVariables t = fv t where
  -- type variables in the constructor are applied
  fv (TApp _ ts) = M.unions (map fv ts)
  fv (TFunc args r _) = M.unions (map fv (r:args))
  fv (TSequence args Nothing) = M.unions (map fv args)
  fv (TSequence args (Just opt)) = M.unions (map fv (opt:args))
  fv (TId _) = M.empty
  fv (TObject props) = M.unions (map (fv.snd) props)
  fv TAny = M.empty
  fv (TRec id t) = M.insert id KindStar (fv t)
  fv (TUnion ts) = M.unions (map fv ts)
  fv (TForall ids _ t) = M.union (M.fromList (zip ids (repeat KindStar)))
                                 (fv t)


isUnion :: Type -> Bool
isUnion (TUnion _) = True
isUnion _ = False

isObject :: Type -> Bool
isObject (TObject _) = True
isObject _ = False