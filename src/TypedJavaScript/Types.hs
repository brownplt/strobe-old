module TypedJavaScript.Types 
  ( Env
  , emptyEnv
  , argEnv
  , unitType
  ) where

import Text.ParserCombinators.Parsec.Pos (initialPos,SourcePos)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.List as L

import TypedJavaScript.Syntax (Type (..))

p = initialPos "TypedJavaScript.Types"

type Env = Map String (Type SourcePos)

emptyEnv :: Env
emptyEnv = M.empty

unitType :: Type SourcePos
unitType = TApp p (TId p "unit") []

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

