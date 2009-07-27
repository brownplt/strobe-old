module BrownPLT.TypedJS.TypeDefinitions
  ( Type(..)
  , RuntimeType (..)
  , RuntimeTypeInfo (..)
  , ArgType (..)
  , Field
  ) where

import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.LocalFlows

-- Type of the arguments array
data ArgType 
  = ArgType [Type] (Maybe Type)
  deriving (Show, Eq, Ord, Data, Typeable)

type Brand = String

type Field = (String, Bool, Type) -- 'True' indicates immutable field

data Type
  = TObject Brand [Field]
  | TAny
  | TArguments ArgType
  | TArrow { tArrowThis :: Type, tArrowArgs :: ArgType, tArrowResult :: Type }
              
  | TId String -- free type variable
  | TIx Int -- bound type variable
  | TApp String [Type]
  | TUnion Type Type
  | TExists Type
  | TForall Type
  | TNamedForall String Type
  deriving (Show, Eq, Ord, Data, Typeable)


