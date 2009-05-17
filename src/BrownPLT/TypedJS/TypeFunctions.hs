module BrownPLT.TypedJS.TypeFunctions
  ( unrestrictEnv
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
