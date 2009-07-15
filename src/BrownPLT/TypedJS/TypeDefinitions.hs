module BrownPLT.TypedJS.TypeDefinitions
  ( Type(..)
  , TypeConstraint (..)
  , RuntimeType (..)
  , RuntimeTypeInfo (..)
  , ArgType (..)
  , Access (..)
  , Field
  ) where

import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.LocalFlows

data TypeConstraint
  = TCSubtype String Type
  deriving (Show, Eq,Ord, Data, Typeable)

type Access = (Bool, Bool) --Access canRead? canWrite?

-- Type of the arguments array
data ArgType 
  = ArgType [Type] (Maybe Type)
  deriving (Show, Eq, Ord, Data, Typeable)

type Brand = String

type Field = (String, Bool, Type) -- 'True' indicates immutable field

data Type
  = TObject Brand [Field]
  | TAny
  | TRec String Type
  | TArguments ArgType
  | TArrow { tArrowThis :: Type, tArrowArgs :: ArgType, tArrowResult :: Type }
              
  | TSequence [Type] (Maybe Type) -- sequence of types (e.g. arguments array)
  | TFunc (Maybe Type) --Nothing if function, Just prototype_type if constr
          [Type]
          Type {- ret type for func, final 'this' type for constr -}
  | TId String -- identifier bound by a TForall or a TRec
  | TApp String [Type]
  | TUnion Type Type
  | TForall [String] [TypeConstraint] Type
  -- | TIndex Type Type String --obj[x] --> TIndex <obj> <x> "x"
  --the first type, 'refined' to the 2nd
  | TEnvId String -- ^a reference to an identifier in the environment
  | TIterator String -- ^iterator for the object referred to by the string
  | TProperty String -- ^property of object given by string, accessed by iter
  | TPrototype String -- ^prototype of the constructor given by string.
  deriving (Show, Eq, Ord, Data, Typeable)


