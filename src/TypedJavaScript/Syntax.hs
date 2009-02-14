-- |JavaScript's syntax.
module TypedJavaScript.Syntax(Expression(..),CaseClause(..),Statement(..),
         InfixOp(..),CatchClause(..),VarDecl(..),JavaScript(..),
         AssignOp(..),Id(..),PrefixOp(..),PostfixOp(..),Prop(..),
         ForInit(..),ForInInit(..),Type(..),showSp) where

import Text.ParserCombinators.Parsec(SourcePos,sourceName,sourceLine) -- used by data JavaScript
import Data.Generics(Data,Typeable)

data JavaScript a
  -- |A script in <script> ... </script> tags.  This may seem a little silly,
  -- but the Flapjax analogue has an inline variant and attribute-inline 
  -- variant.
  = Script a [Statement a] 
  deriving (Data,Typeable,Eq,Ord)

data Id a = Id a String deriving (Ord,Data,Typeable)


data Type a = TObject a [(Id a, Type a)] -- | TExpr a (Expression a)               
              | TFunc a (Maybe (Type a)) {- type of this -} 
                        [Type a] {- required args -} 
                        [Type a] {- optional args -}
                        (Maybe (Type a)) {- optional var arg -}
                        (Type a) {- ret type -}
              | TId a String -- an Id defined through a 'type' statement
              | TApp a (Type a) [Type a]
    deriving (Data,Typeable,Ord)

--equalities:
instance Eq (Id a) where
  Id _ s1 == Id _ s2 = s1 == s2
-- TODO: Add a type for constructors.
instance Eq (Type a) where
  TObject _ props == TObject _ props2 = all id (zipWith (==) props props2)
  TId _ s == TId _ s2                 = s == s2
  TApp _ c1 v1 == TApp _ c2 v2        = c1 == c2 && v1 == v2
  TFunc _ tt1 req1 opt1 var1 ret1 ==
    TFunc _ tt2 req2 opt2 var2 ret2   = tt1 == tt2 && req1 == req2 && 
                                        opt1 == opt2 && var1 == var2 && 
                                        ret1 == ret2
  t1 == t2                            = False

-- http://developer.mozilla.org/en/docs/
--   Core_JavaScript_1.5_Reference:Operators:Operator_Precedence
data InfixOp = OpLT | OpLEq | OpGT | OpGEq  | OpIn  | OpInstanceof | OpEq | OpNEq
             | OpStrictEq | OpStrictNEq | OpLAnd | OpLOr 
             | OpMul | OpDiv | OpMod  | OpSub | OpLShift | OpSpRShift
             | OpZfRShift | OpBAnd | OpBXor | OpBOr | OpAdd
    deriving (Data,Typeable,Eq,Ord,Enum)

data AssignOp = OpAssign | OpAssignAdd | OpAssignSub | OpAssignMul | OpAssignDiv
  | OpAssignMod | OpAssignLShift | OpAssignSpRShift | OpAssignZfRShift
  | OpAssignBAnd | OpAssignBXor | OpAssignBOr
  deriving (Data,Typeable,Eq,Ord)

data PrefixOp = PrefixInc | PrefixDec | PrefixLNot | PrefixBNot | PrefixPlus
  | PrefixMinus | PrefixTypeof -- | PrefixVoid 
  | PrefixDelete
  deriving (Data,Typeable,Eq,Ord)
  
data PostfixOp 
  = PostfixInc | PostfixDec
  deriving (Data,Typeable,Eq,Ord)

--property within an object literal
--TODO: remove PropString?
data Prop a 
  = PropId a (Id a) | PropString a String | PropNum a Integer
  deriving (Data,Typeable,Ord)

instance Eq (Prop a) where
  x == y = (toStr x) == (toStr y) where
    toStr = \p -> case p of 
                      PropId _ (Id _ s) -> s
                      PropString _ s -> s
                      PropNum _ i -> show i

data Expression a
  = StringLit a String
  | RegexpLit a String Bool {- global? -} Bool {- case-insensitive? -}
  | NumLit a Double -- pg. 5 of ECMA-262
  | IntLit a Int    -- int/double distinction. TODO: parse these.
  | BoolLit a Bool
  | NullLit a
  | ArrayLit a [Expression a]
  | ObjectLit a [(Prop a, Maybe (Type a), Expression a)] --optional type annotations on object literals
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
  | CallExpr a (Expression a) [Expression a]
  | FuncExpr a [Id a] {- arg names -} 
               (Type a)
               (Statement a)    {- body -}
  -- | StaticTypeofExpr a (Expression a) -- the <> operator (<5> evaluates to int)
  deriving (Data,Typeable,Eq,Ord)

data CaseClause a 
  = CaseClause a (Expression a) [Statement a]
  | CaseDefault a [Statement a]
  deriving (Data,Typeable,Eq,Ord)
  
data CatchClause a 
  = CatchClause a (Id a) (Statement a) 
  deriving (Data,Typeable,Eq,Ord)

data VarDecl a 
  = VarDecl a (Id a) (Type a)
  | VarDeclExpr a (Id a) (Maybe (Type a)) (Expression a)
  deriving (Data,Typeable,Eq,Ord)
  
data ForInit a
  = NoInit
  | VarInit [VarDecl a]
  | ExprInit (Expression a)
  deriving (Data,Typeable,Eq,Ord)

data ForInInit a
 -- |These terms introduce a name to the enclosing function's environment.
 -- Without a type declaration, we can't return a 'RawEnv' without some
 -- type inference.  Save type inference for later.
 = ForInVar (Id a) (Type a)
 | ForInNoVar (Id a) 
 deriving (Data,Typeable,Eq,Ord)

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
  -- TODO: add generics to functions/constructors?
  -- | FunctionStmt a (Id a) {-name-} [(Id a, Type a)] {-args-} (Maybe (Type a)) {-ret type-}  (Statement a) {-body-}
  | ConstructorStmt a (Id a) {-name-} 
                      [(Id a, Type a)] {- required args -}
                      [(Id a, Type a)] {- optional args -}
                      (Maybe (Id a, Type a)) {- optional var arg -}
                      (Statement a) {-body-}
  | TypeStmt a (Id a) (Type a) -- e.g. type Point :: {x :: int, y :: int};
  deriving (Data,Typeable,Eq,Ord)  
  
showSp :: SourcePos -> String
showSp pos = (sourceName pos) ++ ":" ++ (show $ sourceLine pos)
  
--external statements should only go in the top-level
{- data Toplevel a
  =  ExternalStmt a (Id a) (Type a) -}


