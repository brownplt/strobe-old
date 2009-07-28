module BrownPLT.TypedJS.TypeDefinitions
  ( Type(..)
  , RuntimeType (..)
  , RuntimeTypeInfo (..)
  , ArgType (..)
  , Field
  , isArrayType
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
  = TObject Brand [Type] [Field]
  | TAny
  | TArguments ArgType
  | TArrow { tArrowThis :: Type, tArrowArgs :: ArgType, tArrowResult :: Type }
  | TId String -- ^type variable as a de Brujin index
  | TIx Int -- ^named type variable
  | TApp String [Type]
  | TUnion Type Type
  | TExists Type
  | TForall Type
  | TNamedForall String Type
  | TIntersect Type Type
  | TConstr [Type] Type Type
  deriving (Show, Eq, Ord, Data, Typeable)


isArrayType (TApp "Array" [_]) = True
isArrayType _ = False
