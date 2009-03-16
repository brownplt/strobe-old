module TypedJavaScript.Types 
  ( Env
  , emptyEnv
  , argEnv
  , undefType
  , inferLit
  , unTVal
  , deconstrFnType
  , applyType
  , freeTIds
  ) where

import TypedJavaScript.Prelude
import Text.ParserCombinators.Parsec.Pos (initialPos,SourcePos)
import TypedJavaScript.PrettyPrint()
import TypedJavaScript.Syntax
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.List as L

import TypedJavaScript.Syntax (Type (..))

p = initialPos "TypedJavaScript.Types"

--maps names to their type... should visible predicates be here?
type Env = Map String (Type SourcePos)

emptyEnv :: Env
emptyEnv = M.empty

undefType :: Type SourcePos
undefType = (TId p "undefined")

-- |Builds the local enviroment of a function.
argEnv :: [(String,Type SourcePos)] -- ^positional arguments
       -> Maybe (String,Type SourcePos) -- ^vararity argument
       -> Env
argEnv posArgs varArg = addVarArg $ L.foldl' addPosArg emptyEnv posArgs where
  addPosArg env (x,t) = M.insertWith'
    (error $ "repeated identifier " ++ x ++ " in an argument list")
    x t env
  addVarArg env = case varArg of
    Nothing -> env
    Just (x,t) -> M.insertWith'
      (error $ "repeated identifier " ++ x ++ " in an argument list")
      x t env

-- |Deconstructs the declared type of a function, returning a list of quantified
-- variables, the types of each argument, and a return type.  As we enrich the
-- type-checker to handle more of a function type, include them here.
deconstrFnType :: Type a -> Maybe ([String],[Type a],Type a,LatentPred a)
deconstrFnType (TFunc _ _ args _ result latentP) = Just ([],args,result,latentP)
deconstrFnType (TForall ids (TFunc _ _ args _ result latentP)) = 
  Just (ids,args,result,latentP)
deconstrFnType _ = Nothing

-- |This is _not_ capture-free.
substType :: String -> Type a -> Type a -> Type a
substType var sub (TForall formals body) 
  | var `elem` formals = TForall formals body
  | otherwise = TForall formals (substType var sub body)
substType var sub (TApp p constr args) = 
  TApp p constr (map (substType var sub) args)
substType var sub (TUnion p ts) = 
  TUnion p (map (substType var sub) ts)
substType var sub (TVal e t) = 
  TVal e t -- should not need to subst
substType var sub (TId p var')
  | var == var' = sub
  | otherwise =  TId p var'
substType var sub (TFunc p Nothing args vararg ret latentP) =
  TFunc p Nothing (map (substType var sub) args)
        (liftM (substType var sub) vararg)
        (substType var sub ret)
        latentP
substType var sub (TObject p fields) =
  TObject p (map (\(v,t) -> (v,substType var sub t)) fields)
substType _ _ (TFunc _ (Just _) _ _ _ _) = 
  error "cannot substitute into functions with this-types"

applyType :: Monad m => Type a -> [Type a] -> m (Type a)
applyType (TForall formals body) actuals = do
  unless (length formals == length actuals) $ do
    fail $ "quantified type has " ++ show (length formals) ++ " variables " ++
           "but " ++ show (length actuals) ++ " were supplied"
  return $ foldr (uncurry substType) body (zip formals actuals)
applyType t [] = return t
applyType t actuals =
  fail $ "type " ++ show t ++ " is not quantified, but " ++ 
         show (length actuals)  ++ " type arguments were supplied"

freeTIds :: Type SourcePos -> S.Set String
freeTIds type_ = 
  everythingBut S.union (mkQ True isNotForall) (mkQ S.empty findTId) type_ where
    isNotForall :: Type SourcePos -> Bool
    isNotForall (TForall _ _) = False
    isNotForall _ = True
 
    findTId :: Type SourcePos -> S.Set String
    findTId (TId _ v) = S.singleton v
    findTId (TForall vars t) = S.difference (freeTIds t) (S.fromList vars)
    findTId _ = S.empty
  

-- |Infers the type of a literal value.  Used by the parser to parse 'literal
-- expressions in types
inferLit :: Monad m 
         => Expression a
         -> m (Type a)
inferLit (StringLit p _) = return (TId p "string")
inferLit (NumLit p _) = return (TId p "double")
inferLit (IntLit p _) = return (TId p "integer")
inferLit (BoolLit p _) = return (TId p "bool")
inferLit expr =
  fail $ "Cannot use as a literal"

unTVal (TVal _ t) = t
unTVal t = error $ "unTVal expected a TVal, received " ++ show t
