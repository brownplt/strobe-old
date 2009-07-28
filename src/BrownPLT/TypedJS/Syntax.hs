-- |JavaScript's syntax.
module BrownPLT.TypedJS.Syntax(Expression(..),CaseClause(..),Statement(..),
         InfixOp(..),CatchClause(..),VarDecl(..),JavaScript(..),
         AssignOp(..),Id(..),PrefixOp(..),UnaryAssignOp(..),Prop(..),
         ForInit(..),ForInInit(..),Type(..)
  , ToplevelStatement(..)
  , LValue (..)
  , ArgType (..)
  , showSp, propToString, unId, eqLit
  ) where

import BrownPLT.TypedJS.Prelude
import qualified Data.Foldable as F
import BrownPLT.JavaScript (InfixOp (..), AssignOp (..), PrefixOp (..), 
  UnaryAssignOp(..))
import BrownPLT.JavaScript.Analysis.ANF (Lit, eqLit)
import BrownPLT.TypedJS.LocalFlows (RuntimeType (..))
import BrownPLT.TypedJS.TypeDefinitions

data JavaScript a
  -- |A script in <script> ... </script> tags.  This may seem a little silly,
  -- but the Flapjax analogue has an inline variant and attribute-inline 
  -- variant.
  = Script a [Statement a] 
  deriving (Eq,Ord)

unId (Id _ s) = s

data Id a = Id a String 
  deriving (Show, Ord, Data, Typeable)


-- the following are constructs which just assign types to IDs, either
-- in the variable environment (ExternalStmt) or in the type
-- environment (TypeStmt).
data ToplevelStatement a 
  = TypeStmt a (Id a) Type
  | ExternalStmt a (Id a) Type
  deriving (Show)


data LatentPred = LPType Type | LPNone
    deriving (Show, Eq, Ord, Data, Typeable)

--equalities:
instance Eq (Id a) where
  Id _ s1 == Id _ s2 = s1 == s2

--property within an object literal
--TODO: remove PropString?
data Prop a 
  = PropId a (Id a) | PropString a String | PropNum a Integer
  deriving (Show, Ord, Data, Typeable)

propToString (PropId _ (Id _ s)) = s
propToString (PropString _ s)    = s
propToString (PropNum _ i)       = show i

instance Eq (Prop a) where
  x == y = (propToString x) == (propToString y) where

data LValue a
  = LVar a String
  | LDot a (Expression a) String
  | LBracket a (Expression a) (Expression a)
  deriving (Show, Eq, Ord, Data, Typeable)

data Expression a
  = StringLit a String
  | RegexpLit a String Bool {- global? -} Bool {- case-insensitive? -}
  | NumLit a Double -- pg. 5 of ECMA-262
  | IntLit a Int    -- int/double distinction. 
  | BoolLit a Bool
  | NullLit a
  | ArrayLit a [Expression a]
  | ObjectLit a [(Prop a, Expression a)]
  | ThisRef a
  | VarRef a (Id a)
  | DotRef a (Expression a) (Id a)
  | BracketRef a (Expression a) {- container -} (Expression a) {- key -}
  | NewExpr a (Expression a) {- constructor -} [Expression a]
  | UnaryAssignExpr a UnaryAssignOp (LValue a)
  | PrefixExpr a PrefixOp (Expression a)
  | InfixExpr a InfixOp (Expression a) (Expression a)
  | CondExpr a (Expression a) (Expression a) (Expression a) --ternary operator
  | AssignExpr a AssignOp (LValue a) (Expression a)
  | ParenExpr a (Expression a)
  | ListExpr a [Expression a] -- expressions separated by ',' 
  | CallExpr a (Expression a) [Type] [Expression a]
  | TyAppExpr a (Expression a) Type
  | FuncExpr a [Id a] {- arg names -} 
               Type --if TFunc, then function. if TConstr, then a constructor.
               (Statement a)    {- body -}
  -- Dataflow analysis may deterine a set of possible runtime types for
  -- certain variable references.
  | AnnotatedVarRef a (Set RuntimeType) String
  -- introducing existential types.  Elimination form in 'VarDecl'
  | PackExpr a (Expression a) Type {- concrete -} Type {- existential -}
  deriving (Show, Eq, Ord, Data, Typeable)

data CaseClause a 
  = CaseClause a (Expression a) [Statement a]
  | CaseDefault a [Statement a]
  deriving (Show, Eq, Ord, Data, Typeable)
  
data CatchClause a 
  = CatchClause a (Id a) (Statement a) 
  deriving (Show, Eq, Ord, Data, Typeable)

data VarDecl a 
  = VarDecl a (Id a) Type
  | VarDeclExpr a (Id a) (Maybe Type) (Expression a)
  | UnpackDecl a (Id a) String Type (Expression a)
  deriving (Show, Eq, Ord, Data, Typeable)
  
data ForInit a
  = NoInit
  | VarInit [VarDecl a]
  | ExprInit (Expression a)
  deriving (Show, Eq, Ord, Data, Typeable)

data ForInInit a
 -- |These terms introduce a name to the enclosing function's environment.
 -- Without a type declaration, we can't return a 'RawEnv' without some
 -- type inference.  Save type inference for later.
 = ForInVar (Id a) 
 | ForInNoVar (Id a) 
 deriving (Show, Eq, Ord, Data, Typeable)

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
  | VarDeclStmt a [VarDecl a]
  -- |@ConstructorStmt loc brand body@
  | ConstructorStmt a (Id a) (Expression a)
  -- |@ExternalFieldStmt loc brand field expr@
  -- corresponds to
  -- @brand.prototype.field = expr@
  | ExternalFieldStmt a (Id a) (Id a) (Expression a)
  deriving (Show, Eq, Ord, Data, Typeable)  
  
showSp :: SourcePos -> String
showSp pos = (sourceName pos) ++ ":" ++ (show $ sourceLine pos) ++ 
  ":" ++ (show $ sourceColumn pos)
