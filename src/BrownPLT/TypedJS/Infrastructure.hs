module BrownPLT.TypedJS.Infrastructure
  ( TypeCheck
  , fatalTypeError
  , runTypeCheck
  , runEnv
  , BoundVar
  , BoundTVar (..)
  , emptyEnv
  , domEnv
  , scopeEnv
  , lookupScopeEnv
  , lookupEnv
  , extendEnv
  , extendsEnv
  , envMap
  , nestEnv
  , EnvM
  , bindTVar
  , lookupTVar
  , freshTVar
  )
  where

import BrownPLT.TypedJS.Prelude
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import BrownPLT.TypedJS.TypeDefinitions
import qualified Data.Map as M

data S = S {
  stateErrors :: [(SourcePos, String)]
}

class MonadReader Env m => EnvM m


instance EnvM (ErrorT String (Reader Env))

instance EnvM (Reader Env)

newtype TypeCheck a = TypeCheck (ErrorT String (Reader Env) a)
  deriving (Monad, MonadError String, MonadReader Env, EnvM)



runTypeCheck :: TypeCheck a -> Either String a
runTypeCheck (TypeCheck m) = runReader (runErrorT m) emptyEnv 

runEnv :: Reader Env a -> a
runEnv m = runReader m emptyEnv


fatalTypeError :: SourcePos -> String -> TypeCheck a
fatalTypeError p msg = fail (printf "%s: %s" (show p) msg)

-- ----------------------------------------------------------------------------
-- Environment
--

type BoundVar = (Type, Int)


data BoundTVar = BoundTVar


data Env = Env {
  eDepth :: Int,
  eVars :: Map String BoundVar,
  eTVars :: Map String BoundTVar,
  eGen :: Int
}


emptyEnv  = Env 0 M.empty M.empty 0


domEnv :: MonadReader Env m
       => m [String]
domEnv = asks (M.keys . eVars)


scopeEnv :: MonadReader Env m => m Int
scopeEnv  = asks eDepth


lookupScopeEnv :: MonadReader Env m
               => SourcePos
               -> String
               -> m (Type, Int)
lookupScopeEnv p x = do
  vars <- asks eVars
  case M.lookup x vars of
    Nothing -> fail $ printf "unbound identifier %s at %s" x (show p)
    Just (t, n) -> return (t, n)


lookupEnv p x = do
  (t, n) <- lookupScopeEnv p x
  return t


extendEnv :: MonadReader Env m
             => String
             -> Type
             -> m a
             -> m a
extendEnv x t m = 
  local (\e -> e { eVars = M.insert x (t, eDepth e) (eVars e) }) m


extendsEnv :: MonadReader Env m
            => [(String, Type)]
            -> m a
            -> m a
extendsEnv binds m = foldr (\(x, t) m -> extendEnv x t m) m binds


envMap :: MonadReader Env m
       => m (Map String Type)
envMap = asks (\e -> M.map fst (eVars e))


nestEnv :: MonadReader Env m
        => m a
        -> m a
nestEnv m = local (\e -> e { eDepth = eDepth e + 1 }) m


bindTVar :: MonadReader Env m
         => String
         -> m a
         -> m a
bindTVar x = local (\e -> e { eTVars = M.insert x BoundTVar (eTVars e) })


lookupTVar :: MonadReader Env m
           => String
           -> m (Maybe BoundTVar)
lookupTVar x = asks (\e -> M.lookup x (eTVars e))


freshTVar :: MonadReader Env m
          => (String -> m a)
          -> m a
freshTVar k = do
  n <- asks eGen
  let x = "#x" ++ show n
  bindTVar x $ local (\e -> e { eGen = eGen e + 1 }) (k x)
