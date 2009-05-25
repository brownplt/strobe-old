-- |JavaScript's syntax.
module TypedJavaScript.Syntax(Expression(..),CaseClause(..),Statement(..),
         InfixOp(..),CatchClause(..),VarDecl(..),JavaScript(..),
         AssignOp(..),Id(..),PrefixOp(..),PostfixOp(..),Prop(..),
         ForInit(..),ForInInit(..),Type(..), VP(..),LatentPred(..),         
         ToplevelStatement(..),
         showSp, propToString, unId, eqLit,
         TypeConstraint (..)) where

import TypedJavaScript.Prelude
import qualified Data.Foldable as F
import BrownPLT.JavaScript (InfixOp (..), AssignOp (..), PrefixOp (..), 
  PostfixOp (..))
import BrownPLT.JavaScript.Analysis.ANF (Lit, eqLit)


data JavaScript a
  -- |A script in <script> ... </script> tags.  This may seem a little silly,
  -- but the Flapjax analogue has an inline variant and attribute-inline 
  -- variant.
  = Script a [Statement a] 
  deriving (Eq,Ord)

unId (Id _ s) = s

data Id a = Id a String 
  deriving (Show, Ord, Data, Typeable)

data TypeConstraint
  = TCSubtype String Type
  deriving (Show, Eq,Ord, Data, Typeable)

data Type
  = TObject Bool --hasSlack
            Bool --isOpenObject ('this' inside a constructor, and f.prototype)
            [(String, Type)]
  | TAny
  | TRec String Type
  | TSequence [Type] (Maybe Type) -- sequence of types (e.g. arguments array)
  | TFunc (Maybe Type) --Nothing if function, Just prototype_type if constr
          [Type]
          Type {- ret type for func, final 'this' type for constr -}
          LatentPred {- latent predicate -} 
  | TId String -- identifier bound by a TForall or a TRec
  | TApp String [Type]
  | TUnion [Type]
  | TForall [String] [TypeConstraint] Type
  -- | TIndex Type Type String --obj[x] --> TIndex <obj> <x> "x"
  --the first type, 'refined' to the 2nd
  | TEnvId String -- ^a reference to an identifier in the environment
  | TIterator String -- ^iterator for the object referred to by the string
  | TProperty String -- ^property of object given by string, accessed by iter
  | TPrototype String -- ^prototype of the constructor given by string.
  deriving (Show, Eq, Ord, Data, Typeable)

-- the following are constructs which just assign types to IDs, either
-- in the variable environment (ExternalStmt) or in the type
-- environment (TypeStmt).
data ToplevelStatement a 
  = TypeStmt a (Id a) Type
  | ExternalStmt a (Id a) Type
  deriving (Show)


data VP = VPId String
        | VPType Type String
        | VPNone
        | VPWeakType Type String --result of "x == 3"
        | VPTypeof String
        | VPNot VP
        | VPLit (Lit SourcePos) Type
        | VPMulti [VP]
    deriving (Show, Ord, Eq)

-- VPId "x" == VPLit 3 (TId "int")
--  becomes:
-- VPType (TVal 3 (TId "int")) "x"
-- when it's true: 
--    restrict x to TVal 3 int
-- when false:
--    remove TVal 3 int from x

-- x --> VPId "x"
-- typeof e where e has vp VPID "x" --> VPTypeof "x"
-- e1 == e2 where e1 has vp VPTypeof "x" and
--  e2 has vp VPLit "number" (TId "String"):
-- VPTypeof "x" == VPLit "number" (TId "string")
--  becomes:
-- VPType (TId "double") "x"

data LatentPred = LPType Type | LPNone
    deriving (Show, Eq, Ord, Data, Typeable)

--equalities:
instance Eq (Id a) where
  Id _ s1 == Id _ s2 = s1 == s2

--property within an object literal
--TODO: remove PropString?
data Prop a 
  = PropId a (Id a) | PropString a String | PropNum a Integer
  deriving (Show, Ord)

propToString (PropId _ (Id _ s)) = s
propToString (PropString _ s)    = s
propToString (PropNum _ i)       = show i

instance Eq (Prop a) where
  x == y = (propToString x) == (propToString y) where

data Expression a
  = StringLit a String
  | RegexpLit a String Bool {- global? -} Bool {- case-insensitive? -}
  | NumLit a Double -- pg. 5 of ECMA-262
  | IntLit a Int    -- int/double distinction. 
  | BoolLit a Bool
  | NullLit a
  | ArrayLit a [Expression a]
  | ObjectLit a [(Prop a, Maybe Type, Expression a)] --optional type annotations on object literals
  | ThisRef a
  | VarRef a (Id a)
  | DotRef a (Expression a) (Id a)
  | BracketRef a (Expression a) {- container -} (Expression a) {- key -}
  | NewExpr a (Expression a) {- constructor -} [Expression a]
  | PostfixExpr a PostfixOp (Expression a)
  | PrefixExpr a PrefixOp (Expression a)
  | InfixExpr a InfixOp (Expression a) (Expression a)
  | CondExpr a (Expression a) (Expression a) (Expression a) --ternary operator
  | AssignExpr a AssignOp (Expression a) (Expression a)
  | ParenExpr a (Expression a)
  | ListExpr a [Expression a] -- expressions separated by ',' 
  | CallExpr a (Expression a) [Type] [Expression a]
  | FuncExpr a [Id a] {- arg names -} 
               Type --if TFunc, then function. if TConstr, then a constructor.
               (Statement a)    {- body -}
  deriving (Show, Eq,Ord)

data CaseClause a 
  = CaseClause a (Expression a) [Statement a]
  | CaseDefault a [Statement a]
  deriving (Show, Eq,Ord)
  
data CatchClause a 
  = CatchClause a (Id a) (Statement a) 
  deriving (Show, Eq,Ord)

data VarDecl a 
  = VarDecl a (Id a) Type
  | VarDeclExpr a (Id a) (Maybe Type) (Expression a)
  deriving (Show, Eq,Ord)
  
data ForInit a
  = NoInit
  | VarInit [VarDecl a]
  | ExprInit (Expression a)
  deriving (Show, Eq,Ord)

data ForInInit a
 -- |These terms introduce a name to the enclosing function's environment.
 -- Without a type declaration, we can't return a 'RawEnv' without some
 -- type inference.  Save type inference for later.
 = ForInVar (Id a) 
 | ForInNoVar (Id a) 
 deriving (Show, Eq,Ord)

data Statement a
  = BlockStmt a [Statement a]
  | EmptyStmt a
  | ExprStmt a (Expression a)
  | IfStmt a (Expression a) (Statement a) (Statement a)
  | IfSingleStmt a (Expression a) (Statement a)
  | SwitchStmt a (Expression a) [CaseClause a]
  | WhileStmt a (Expression a) (Statement a)
  | DoWhileStmt a (Statement a) (Expression a)
  | BreakStmt a (Maybe (Id a))
  | ContinueStmt a (Maybe (Id a))
  | LabelledStmt a (Id a) (Statement a)
  | ForInStmt a (ForInInit a) (Expression a) (Statement a)
  | ForStmt a (ForInit a)        
              (Maybe (Expression a)) -- test
              (Maybe (Expression a)) -- increment
              (Statement a)          -- body
  | TryStmt a (Statement a) {-body-} [CatchClause a] {-catches-}
      (Maybe (Statement a)) {-finally-}
  | ThrowStmt a (Expression a)
  | ReturnStmt a (Maybe (Expression a))
  -- | WithStmt a (Expression a) (Statement a)
  | VarDeclStmt a [VarDecl a]
  -- FunctionStatements turn into expressions with an assignment. 
  -- | FunctionStmt a (Id a) {-name-} [(Id a, Type)] {-args-} (Maybe Type) {-ret type-}  (Statement a) {-body-}
{-  | ConstructorStmt a (Id a) {-name-} 
                      [(Id a, Type)] {- required args -}
                      [(Id a, Type)] {- optional args -}
                      (Maybe (Id a, Type)) {- optional var arg -}
                      (Statement a) {-body-} -}
  deriving (Show, Eq,Ord)  
  
showSp :: SourcePos -> String
showSp pos = (sourceName pos) ++ ":" ++ (show $ sourceLine pos) ++ 
  ":" ++ (show $ sourceColumn pos)
