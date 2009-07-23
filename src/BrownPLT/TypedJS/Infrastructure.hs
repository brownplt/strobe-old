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
  , bindTVars
  , lookupTVar
  , freshTVar
  -- * Brand Store
  , newRootBrand
  , extendBrand
  , isSubbrand
  )
  where

import BrownPLT.TypedJS.Prelude
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import BrownPLT.TypedJS.TypeDefinitions
import BrownPLT.TypedJS.PrettyPrint (renderType)
import qualified Data.Map as M

data S = S {
  stateErrors :: [(SourcePos, String)]
}

class (MonadReader Env m, MonadState BrandStore m) => EnvM m


instance EnvM (StateT BrandStore (Reader Env))
instance EnvM (ErrorT String (StateT BrandStore (Reader Env)))


newtype TypeCheck a
  = TypeCheck (ErrorT String (StateT BrandStore (Reader Env)) a)
  deriving (Monad, MonadError String, MonadState BrandStore, MonadReader Env, 
            EnvM)



runTypeCheck :: TypeCheck a -> Either String a
runTypeCheck (TypeCheck m) = 
  runReader (evalStateT (runErrorT m) emptyBrandStore) emptyEnv 

runEnv :: StateT BrandStore (Reader Env) a -> a
runEnv m = runReader (evalStateT m emptyBrandStore) emptyEnv


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
    Nothing -> fail $ printf "unbound identifier %s at %s" 
                             x (show p)
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


bindTVars :: MonadReader Env m
          => [String]
          -> m a
          -> m a
bindTVars tvars m = foldr bindTVar m tvars


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


-- ----------------------------------------------------------------------------

data BrandStore = BrandStore {
  -- |Maps brand names to their complete type and the name of the brand they
  -- extend.  All user-defined brands extend @Object@, though the builtin
  -- DOM objects do not.
  brandStoreDict :: Map String (Type, Maybe String)
}


emptyBrandStore :: BrandStore
emptyBrandStore = BrandStore M.empty


newRootBrand :: MonadState BrandStore m
             => Type -- ^expected @TObject@
             -> m ()
newRootBrand ty@(TObject brand fields) = do
  s <- get
  let dict = brandStoreDict s
  case M.lookup brand dict of
    Nothing -> put $ s { brandStoreDict = M.insert brand (ty, Nothing) dict }
    Just (ty', _) -> fail $ printf "constructor %s is already defined with the\
                                   \ type %s" brand (renderType ty')
newRootBrand ty =
  fail $ printf "newRootBrand: expected (TObject ...), received %s" 
                (renderType ty)


insertField :: String -- ^field name
            -> Type   -- ^field type
            -> [Field]
            -> Maybe [Field]
insertField name ty [] = return [(name, False, ty)]
insertField name ty ((name', ro, ty'):rest)
  | name' < name = do
    rest' <- insertField name ty rest
    return ((name', ro, ty'):rest')
  | name' == name = 
    Nothing
  | name' > name = do
    return ((name, False, ty):(name', ro, ty'):rest)


extendBrand :: MonadState BrandStore m
            => String -- ^brand name
            -> String -- ^field name
            -> Type   -- ^field type
            -> m ()
extendBrand brand field ty = do
  s <- get
  let dict = brandStoreDict s
  case M.lookup brand dict of
    Just (TObject _ fields, parent) -> case insertField field ty fields of
      Just fields' -> 
        put $ s { brandStoreDict = 
                  M.insert brand (TObject brand fields', parent) dict }
      Nothing -> fail $ printf "constructor %s already has a field named %s"
                               brand field
    Just (t, _) -> error $ printf 
      "extendBrand: brand store inconsistent, %s has the type %s"
      brand (renderType t)
    Nothing -> fail $ printf "constructor %s is not defined" brand


isSubbrand :: MonadState BrandStore m
           => String -- ^candidate subbrand
           -> String -- ^candidate superbrand
           -> m Bool
isSubbrand sub sup = do
  s <- get
  let dict = brandStoreDict s
  -- Traverse the brand heirarchy up from sub, until we find sup or reach the
  -- root.  @newBrand@ prevents us from creating cycles, so this process will
  -- terminate.
  let traverse brand 
        | brand == sup = True
        | otherwise = case M.lookup brand dict of
            Just (_, Just parent) -> traverse parent
            Just (_, Nothing) -> False
            Nothing -> error $ printf 
              "isSubbrand : brand store inconsistent, %s not found" brand
  return (traverse sub)
