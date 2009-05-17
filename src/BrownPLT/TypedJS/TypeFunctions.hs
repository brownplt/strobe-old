module BrownPLT.TypedJS.TypeFunctions
  ( unrestrictEnv
  , unrestrict
  , freeTypeVariables
  ) where

import qualified Data.Map as M

import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.TypeDefinitions

import TypedJavaScript.Types

-- |Removes 'TRefined'
unrestrict :: Type -> Type
unrestrict t = case t of
  TRefined t' _ -> unrestrict t' -- Is this necessary?
  TObject props -> TObject (map f props)
    where f (s, t') = (s, unrestrict t')
  TAny -> TAny
  TRec s t' -> TRec s (unrestrict t')
  TSequence ts yt -> TSequence (map unrestrict ts) (liftM unrestrict yt)
  TFunc ts rt lp -> TFunc (map unrestrict ts) (unrestrict rt) lp
  TId s -> TId s
  TApp c ts -> TApp c (map unrestrict ts)
  TUnion ts -> TUnion (map unrestrict ts)
  TForall vs tcs t' -> TForall vs tcs (unrestrict t')
  TEnvId s -> TEnvId s


-- |Removes 'TRefined' from an environment.
unrestrictEnv :: Env -> Env
unrestrictEnv env = M.map f env
  where f Nothing = Nothing
        f (Just (t, vp)) = Just (unrestrict t, vp)


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
  fv (TRefined t1 t2) = M.union (fv t1) (fv t2)
