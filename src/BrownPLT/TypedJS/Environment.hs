module BrownPLT.TypedJS.Environment 
  where

import BrownPLT.TypedJS.Prelude
import qualified Data.Map as M
import BrownPLT.TypedJS.TypeTheory
import BrownPLT.TypedJS.TypeDefinitions
import qualified Data.Set as S


data Env = Env Int (Map String (Type, Int))


emptyEnv :: Env
emptyEnv = Env 0 M.empty

domEnv :: Env -> [String]
domEnv (Env _ dict) = M.keys dict

lookupEnv :: Monad m
          => SourcePos 
          -> Env
          -> String
          -> m Type
lookupEnv loc env x = do
  (t, n) <- lookupScopeEnv loc env x
  return t


lookupScopeEnv :: Monad m
               => SourcePos
               -> Env
               -> String
               -> m (Type, Int)
lookupScopeEnv loc (Env _ dict) x = case M.lookup x dict of
  Nothing -> fail $ printf "unbound identifier %s at %s" x (show loc)
  Just (t, n) -> return (t, n)


scopeEnv :: Env -> Int
scopeEnv (Env n _) = n


extendEnv :: Env -> String -> Type -> Env
extendEnv (Env n dict) x t = Env n (M.insert x (t, n) dict)


extendsEnv :: Env -> [(String, Type)] -> Env
extendsEnv env binds = foldr (\(x, t) env -> extendEnv env x t) env binds


-- runtimeEnv :: Env -> Map String RuntimeTypeInfo
runtimeEnv (Env _ dict) = M.map (runtime.fst) dict


nestEnv :: Env -> Env
nestEnv (Env n dict) = Env (n + 1) dict
