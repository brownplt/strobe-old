-- |JavaScript's syntax.
module BrownPLT.TypedJS.Syntax
  ( Expression(..)
  , CaseClause(..)
  , ConstrFieldAsgn(..)
  , constrBodyStmt
  , Statement(..)
  , InfixOp(..)
  , CatchClause(..)
  , VarDecl(..)
  , AssignOp(..)
  , Id(..)
  , PrefixOp(..)
  , UnaryAssignOp(..)
  , Prop(..)
  , ForInit(..)
  , ForInInit(..)
  , Type(..)
  , LValue (..)
  , ArgType (..)
  , TopLevel (..)
  , unId
  ) where

import BrownPLT.TypedJS.Prelude
import qualified Data.Foldable as F
import BrownPLT.JavaScript (InfixOp (..), AssignOp (..), PrefixOp (..), 
  UnaryAssignOp(..))
import BrownPLT.JavaScript.Analysis.ANF (Lit, eqLit)
import BrownPLT.TypedJS.LocalFlows (RuntimeType (..))
import BrownPLT.TypedJS.TypeDefinitions


data Id a = Id a String 
  deriving (Show, Eq, Ord, Data, Typeable)


data LatentPred = LPType Type | LPNone
    deriving (Show, Eq, Ord, Data, Typeable)


data Prop a 
  = PropId a (Id a) 
  | PropString a String 
  | PropNum a Integer
  deriving (Show, Eq, Ord, Data, Typeable)


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
  | UnpackDecl a (Id a) [String] (Expression a)
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
  deriving (Show, Eq, Ord, Data, Typeable)


data ConstrFieldAsgn a
  = ConstrFieldAsgn a String (Expression a)
  deriving (Show, Eq, Ord, Data, Typeable)

asgnToStmt (ConstrFieldAsgn p n x) =
  ExprStmt p (AssignExpr p OpAssign (LDot p (ThisRef p) n) x)
--given a constructorstmt, turn fieldasgns into normal stmts and put in a block
constrBodyStmt p asgns body = 
  BlockStmt p $ (map asgnToStmt asgns) ++ [body]

data TopLevel a
  -- |@ConstructorStmt loc brand args constrTy asgnbody body@
  -- asgnbody is all the assignments to fields of constructors
  -- body is the regularly scheduled programming
  = ConstructorStmt a String [String] Type [ConstrFieldAsgn a] (Statement a)
  -- |@ExternalFieldStmt loc brand field expr@
  -- corresponds to
  -- @brand.prototype.field = expr@
  | ExternalFieldStmt a (Id a) (Id a) (Expression a)
  | TopLevelStmt (Statement a)
  -- |@ImportStmt loc name isAssumed ty@
  -- If @isAssumed@ is @true@, we do not use contracts.
  | ImportStmt a (Id a) Bool Type
  | ImportConstrStmt a (Id a) Bool Type
  deriving (Show, Eq, Ord, Data, Typeable)
  

unId (Id _ s) = s
