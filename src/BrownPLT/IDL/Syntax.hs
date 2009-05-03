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
