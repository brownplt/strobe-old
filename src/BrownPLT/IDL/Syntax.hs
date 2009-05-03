module BrownPLT.IDL.Syntax where


type Id = String


data Type
  = TInt
  | TBool
  | TVoid
  | TId String
  deriving (Show)


data Value 
  = VInt Integer
  deriving (Show)


-- In the spirit of s-expressions, everything is a definition.
data Definition
  = Const Type Id Value
  | Attr Bool {- read-only? -} Type Id
  | Method Type Id [(Type, Id)]
  | Interface {
      interfaceName :: Id,
      interfaceInherits :: Maybe Id,
      interfaceItems :: [Definition]
    }
  deriving (Show)

definitionName :: Definition -> Id
definitionName def = case def of
  Const _ id _ -> id
  Attr _ _ id -> id
  Method _ id _ -> id
  Interface id _ _ -> id
