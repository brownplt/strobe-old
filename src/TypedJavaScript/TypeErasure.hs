-- |Erases types, compiling Typed JavaScript to JavaScript.
module TypedJavaScript.TypeErasure
  ( eraseTypesExpr
  , eraseTypesStmts
  , eraseTypes
  ) where

import Prelude hiding (id)
import TypedJavaScript.Prelude

import qualified BrownPLT.JavaScript as JS
import TypedJavaScript.Syntax

eraseTypesExpr :: Expression a -> JS.Expression a
eraseTypesExpr = expr

eraseTypesStmts :: [Statement a] -> [JS.Statement a]
eraseTypesStmts = map stmt

id (Id p s) = JS.Id p s

prop (PropId p x) = JS.PropId p (id x)
prop (PropString p s) = JS.PropString p s
prop (PropNum p n) = JS.PropNum p n


lvalue (LVar p x) = JS.VarRef p (JS.Id p x)
lvalue (LDot p e x) = JS.DotRef p (expr e) (JS.Id p x)
lvalue (LBracket p e1 e2) = JS.BracketRef p (expr e1) (expr e2)


expr (StringLit p s) = JS.StringLit p s
expr (RegexpLit p s g ci) = JS.RegexpLit p s g ci
expr (NumLit p n) = JS.NumLit p n
expr (IntLit p n) = JS.IntLit p (fromIntegral n)
expr (BoolLit p b) = JS.BoolLit p b
expr (NullLit p) = JS.NullLit p
expr (ArrayLit p es) = JS.ArrayLit p (map expr es)
expr (ObjectLit p props) = JS.ObjectLit p (map erase props) where
  erase (p,_,e) = (prop p, expr e)
expr (ThisRef p) = JS.ThisRef p
expr (VarRef p x) = JS.VarRef p (id x)
expr (DotRef p e x) = JS.DotRef p (expr e) (id x)
expr (BracketRef p e1 e2) = JS.BracketRef p (expr e1) (expr e2)
expr (NewExpr p e1 es) = JS.NewExpr p (expr e1) (map expr es)
expr (PostfixExpr p op e) = JS.PostfixExpr p op (expr e)
expr (PrefixExpr p op e) = JS.PrefixExpr p op (expr e)
expr (InfixExpr p op e1 e2) = JS.InfixExpr p op (expr e1) (expr e2)
expr (CondExpr p e1 e2 e3) = JS.CondExpr p (expr e1) (expr e2) (expr e3)
expr (AssignExpr p op e1 e2) = JS.AssignExpr p op (lvalue e1) (expr e2)
expr (ParenExpr p e) = JS.ParenExpr p (expr e)
expr (ListExpr p es) = JS.ListExpr p (map expr es)
expr (CallExpr p e _ es) = JS.CallExpr p (expr e) (map expr es)
expr (FuncExpr p ids _ s) = JS.FuncExpr p (map id ids) (stmt s)

caseClause (CaseClause p e ss) = JS.CaseClause p (expr e) (map stmt ss)
caseClause (CaseDefault p ss) = JS.CaseDefault p (map stmt ss)

catchClause (CatchClause p x s) = JS.CatchClause p (id x) (stmt s)

varDecl (VarDecl p x _) = JS.VarDecl p (id x) Nothing
varDecl (VarDeclExpr p x _ e) = JS.VarDecl p (id x) (Just $ expr e)

forInit NoInit = JS.NoInit
forInit (VarInit ds) = JS.VarInit (map varDecl ds)
forInit (ExprInit e) = JS.ExprInit (expr e)

forInInit (ForInVar x) = JS.ForInVar (id x)
forInInit (ForInNoVar x) = JS.ForInNoVar (id x)


stmt (BlockStmt p ss) = JS.BlockStmt p (map stmt ss)
stmt (EmptyStmt p) = JS.EmptyStmt p
stmt (ExprStmt p e) = JS.ExprStmt p (expr e)
stmt (IfStmt p e s1 s2) = JS.IfStmt p (expr e) (stmt s1) (stmt s2)
stmt (IfSingleStmt p e s) = JS.IfSingleStmt p (expr e) (stmt s)
stmt (SwitchStmt p e cs) = JS.SwitchStmt p (expr e) (map caseClause cs)
stmt (WhileStmt p e s) = JS.WhileStmt p (expr e) (stmt s)
stmt (DoWhileStmt p s e) = JS.DoWhileStmt p (stmt s) (expr e)
-- x :: Maybe Id
-- id :: Id -> JS.Id
-- liftM id :: Maybe Id -> Maybe (JS.Id)
stmt (BreakStmt p x) = JS.BreakStmt p (liftM id x)
stmt (ContinueStmt p x) = JS.ContinueStmt p (liftM id x)
stmt (LabelledStmt p x s) = JS.LabelledStmt p (id x) (stmt s)
stmt (ForInStmt p i e s) = JS.ForInStmt p (forInInit i) (expr e) (stmt s)
stmt (ForStmt p init test incr s) =
  JS.ForStmt p (forInit init) (liftM expr test) (liftM expr incr) (stmt s)
stmt (TryStmt p s1 cs s2) = 
  JS.TryStmt p (stmt s1) (map catchClause cs) (liftM stmt s2)
stmt (ThrowStmt p e) = JS.ThrowStmt p (expr e)
stmt (ReturnStmt p e) = JS.ReturnStmt p (liftM expr e)
stmt (VarDeclStmt p ds) = JS.VarDeclStmt p (map varDecl ds)
--stmt (TypeStmt{}) = error "type-erasure undefined for type statements"

eraseTypes :: [Statement a] -> [JS.Statement a]
eraseTypes = map stmt
