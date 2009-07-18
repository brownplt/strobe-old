-- |Returns the locally declared variables in a function, along with their type
-- annotations.  If the variable does not have a type annotation, the expression
-- is returned.  This module does not check for duplicate variable declarations.
module BrownPLT.TypedJS.LocalVars
  ( localVars
  , Binding
  ) where

import BrownPLT.TypedJS.Prelude
import TypedJavaScript.Syntax

type Binding = (String, Either (Expression SourcePos) Type)
 

varDecl :: VarDecl SourcePos -> Binding
varDecl (VarDecl _ x t) = (unId x, Right t)
varDecl (VarDeclExpr _ x (Just t) _) = (unId x, Right t)
varDecl (VarDeclExpr _ x Nothing e) = (unId x, Left e)
 
 
caseClause :: CaseClause SourcePos -> [Binding]
caseClause cc = case cc of
  CaseClause _ e ss -> concatMap stmt ss
  CaseDefault _ ss -> concatMap stmt ss
 

catchClause :: CatchClause SourcePos -> [Binding]
catchClause (CatchClause _ id s) = stmt s


forInit :: ForInit SourcePos -> [Binding]
forInit (VarInit decls) = map varDecl decls
forInit _ = []
 
 
stmt :: Statement SourcePos -> [Binding]
stmt s = case s of
  BlockStmt _ ss -> concatMap stmt ss
  EmptyStmt _ -> []
  ExprStmt _ _ -> []
  IfStmt _ _ s1 s2 -> stmt s1 ++ stmt s2
  IfSingleStmt _ _ s -> stmt s
  SwitchStmt _ _ cases -> concatMap caseClause cases
  WhileStmt _ _ s -> stmt s
  DoWhileStmt _ s _ -> stmt s
  BreakStmt _ _ -> []
  ContinueStmt _ _ -> []
  LabelledStmt _ _ s -> stmt s
  ForInStmt _ _ _ s -> stmt s
  ForStmt _ fi _ _ s -> forInit fi ++ stmt s
  TryStmt _ s catches ms ->
    stmt s ++ (concatMap catchClause catches) ++ (maybe [] stmt ms)
  ThrowStmt _ _ -> []
  ReturnStmt _ _ -> []
  VarDeclStmt _ decls -> map varDecl decls


localVars :: Statement SourcePos
          -> [Binding]
localVars s = stmt s
