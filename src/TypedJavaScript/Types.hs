module TypedJavaScript.Types 
  ( Env
  , emptyEnv
  , argEnv
  , unitType
  , inferLit
  , eqLit
  , unTVal
  ) where

import Text.ParserCombinators.Parsec.Pos (initialPos,SourcePos)
import TypedJavaScript.Syntax (Expression (..))
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.List as L

import TypedJavaScript.Syntax (Type (..))

p = initialPos "TypedJavaScript.Types"

--maps names to their type... should visible predicates be here?
type Env = Map String (Type SourcePos)

emptyEnv :: Env
emptyEnv = M.empty

unitType :: Type SourcePos
unitType = (TId p "unit")

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

eqLit :: Expression a -> Expression a -> Bool
eqLit (StringLit _ s1) (StringLit _ s2) = s1 == s2
eqLit (NumLit _ n1) (NumLit _ n2) = n1 == n2
eqLit (IntLit _ n1) (IntLit _ n2) = n1 == n2
eqLit (BoolLit _ b1) (BoolLit _ b2) = b1 == b2
eqLit _ _ = False

unTVal (TVal _ t) = t
unTVal t = error $ "unTVal expected a TVal, received " ++ show t
