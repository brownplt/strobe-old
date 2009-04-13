-- |JavaScript's syntax.
module TypedJavaScript.Syntax(Expression(..),CaseClause(..),Statement(..),
         InfixOp(..),CatchClause(..),VarDecl(..),JavaScript(..),
         AssignOp(..),Id(..),PrefixOp(..),PostfixOp(..),Prop(..),
         ForInit(..),ForInInit(..),Type(..), VP(..),LatentPred(..),         
         ToplevelStatement(..),
         showSp, propToString, unId, eqLit,
         typePos, TypeConstraint (..)) where

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

data Id a = Id a String deriving (Ord,Data,Typeable)

data TypeConstraint
  = TCSubtype (Type SourcePos) (Type SourcePos)
  deriving (Eq,Ord)

--TODO: add TExtend syntax ( <- operator), and a syntax for constructors
data Type a 
  = TObject a [(Id a, Type a)]
  | TFunc a (Maybe (Type a)) {- type of this -} 
            [Type a] {- required args -} 
            (Maybe (Type a)) {- optional var arg -}
            (Type a) {- ret type -}
            (LatentPred a) {- latent predicate -} 
  | TId a String -- an Id defined through a 'type' statement
  | TApp a (Type a) [Type a]
  | TUnion a [Type a]
  | TVal (Lit a) (Type a)
  | TForall [String] [TypeConstraint] (Type a)
  -- | TIndex (Type a) (Type a) String --obj[x] --> TIndex <obj> <x> "x"
  --the first type, 'refined' to the 2nd
  | TRefined (Type a) (Type a) 
  
  deriving (Ord)

-- the following are constructs which just assign types to IDs, either
-- in the variable environment (ExternalStmt) or in the type
-- environment (TypeStmt).
data ToplevelStatement a 
  = TypeStmt a (Id a) (Type a)
  | ExternalStmt a (Id a) (Type a)

-- hack-ish to avoid parametrizing VP. 
data VP = VPId String
        | VPType (Type SourcePos) String
        | VPNone
        --TODO: Justify the following VPs:
        | VPTypeof String
        | VPNot VP
        | VPLit (Lit SourcePos) (Type SourcePos)
        | VPMulti [VP]
    deriving (Ord, Eq)

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

data LatentPred a = LPType (Type a) | LPNone
    deriving (Ord)

--equalities:
instance Eq (Id a) where
  Id _ s1 == Id _ s2 = s1 == s2


instance Eq (Type a) where
  TObject _ props1 == TObject _ props2 = 
    (hasall props1 props2) && (hasall props2 props1) where
      hasall p1 p2 = all
        (\(o2id@(Id _ o2propname), o2proptype) -> maybe
          False ((==) o2proptype) (lookup o2id p1))
        p2
     -- all id (zipWith (==) props props2)
  TUnion _ types1 == TUnion _ types2 =
    (hasall types1 types2) && (hasall types2 types1) where
      hasall t1s t2s = all (\t2 -> any ((==) t2) t1s) t2s
  TId _ s == TId _ s2                 = s == s2
  TApp _ c1 v1 == TApp _ c2 v2        = c1 == c2 && v1 == v2
  TFunc _ tt1 req1 var1 ret1 lp1 ==
    TFunc _ tt2 req2 var2 ret2 lp2 = tt1 == tt2 && req1 == req2 && 
                                          var1 == var2 && 
                                          ret1 == ret2 && lp1 == lp2
  TVal x t == TVal x2 t2 = x `eqLit` x2 && t == t2
  t1 == t2                            = False

instance Eq (LatentPred a) where
  LPType t1    == LPType t2     = t1 == t2
  LPNone       == LPNone        = True
  l1           == l2            = False

--property within an object literal
--TODO: remove PropString?
--TODO: would it be possible to write an "extract source pos" generic function
--      that would take any one of these and return its source position?
data Prop a 
  = PropId a (Id a) | PropString a String | PropNum a Integer
  deriving (Ord)

propToString (PropId _ (Id _ s)) = s
propToString (PropString _ s)    = s
propToString (PropNum _ i)       = show i

instance Eq (Prop a) where
  x == y = (propToString x) == (propToString y) where

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
  | CallExpr a (Expression a) [Type a] [Expression a]
  | FuncExpr a [Id a] {- arg names -} 
               (Type a)
               (Statement a)    {- body -}
  deriving (Eq,Ord)

data CaseClause a 
  = CaseClause a (Expression a) [Statement a]
  | CaseDefault a [Statement a]
  deriving (Eq,Ord)
  
data CatchClause a 
  = CatchClause a (Id a) (Statement a) 
  deriving (Eq,Ord)

data VarDecl a 
  = VarDecl a (Id a) (Type a)
  | VarDeclExpr a (Id a) (Maybe (Type a)) (Expression a)
  deriving (Eq,Ord)
  
data ForInit a
  = NoInit
  | VarInit [VarDecl a]
  | ExprInit (Expression a)
  deriving (Eq,Ord)

data ForInInit a
 -- |These terms introduce a name to the enclosing function's environment.
 -- Without a type declaration, we can't return a 'RawEnv' without some
 -- type inference.  Save type inference for later.
 = ForInVar (Id a) 
 | ForInNoVar (Id a) 
 deriving (Eq,Ord)

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
{-  | ConstructorStmt a (Id a) {-name-} 
                      [(Id a, Type a)] {- required args -}
                      [(Id a, Type a)] {- optional args -}
                      (Maybe (Id a, Type a)) {- optional var arg -}
                      (Statement a) {-body-} -}
  deriving (Eq,Ord)  
  
showSp :: SourcePos -> String
showSp pos = (sourceName pos) ++ ":" ++ (show $ sourceLine pos)
  
-- TODO: Make this function unnecessary.
typePos :: (Type SourcePos) -> SourcePos
typePos t = case t of
  TObject p _ -> p
  TFunc p _ _ _ _ _ -> p
  TId p _ -> p
  TApp p _ _ -> p
  TUnion p _ -> p
  TVal _ t' -> typePos t'
  TForall _ _ t' -> typePos t'
  TRefined _ t' -> typePos t'
