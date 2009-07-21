module BrownPLT.TypedJS.TypeCheckEngine
  ( TypeCheck
  , typeError
  , fatalTypeError
  , runTypeCheck
  ) where

import BrownPLT.TypedJS.Prelude
import Control.Monad.Reader

data S = S {
  stateErrors :: [(SourcePos, String)]
}


data TypeCheck a = TypeCheck (S  -> (S, Either String a))


runTypeCheck :: TypeCheck a -> Either [(SourcePos, String)] a
runTypeCheck (TypeCheck f) = case f (S []) of
  (S [], Right a) -> Right a
  (S errs, Right _) -> Left errs
  (S errs, Left err) -> Left $ (noPos, err) : errs


instance Monad TypeCheck where

  return a = TypeCheck $ \s -> (s, Right a)

  fail str = TypeCheck $ \s -> (s, Left str)

  (TypeCheck f) >>= g = TypeCheck $ \s -> case f s of
    (s', Left str) -> (s', Left str)
    (s', Right a) -> case g a of
      TypeCheck f -> f s'


getState :: TypeCheck S
getState = TypeCheck $ \s -> (s, Right s)


putState :: S -> TypeCheck ()
putState s = TypeCheck $ \_ -> (s, Right ())
  

typeError :: SourcePos
          -> String
          -> TypeCheck ()
typeError loc msg = do
  s <- getState
  putState $ s { stateErrors = (loc, msg):(stateErrors s) }

fatalTypeError :: SourcePos -> String -> TypeCheck a
fatalTypeError p msg = fail (printf "%s: %s" (show p) msg)
