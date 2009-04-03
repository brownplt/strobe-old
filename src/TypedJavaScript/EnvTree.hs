module TypedJavaScript.EnvTree where

import Prelude hiding (catch)
import TypedJavaScript.Prelude
import TypedJavaScript.Syntax
import qualified Data.Map as M

data EnvTree = EnvTree {
  envTreeEnv      :: Env,
  envTreeSubtrees :: [EnvTree]
}

type Env = Map SourcePos [Type SourcePos]

empty :: EnvTree
empty = EnvTree (M.empty) []

unions :: [EnvTree] -> EnvTree
unions et = EnvTree (M.unions $ map envTreeEnv et)
                    (concatMap envTreeSubtrees et)

buildEnvTree :: [Statement SourcePos] -> EnvTree
buildEnvTree stmts = envTree where
  envtrees = map stmt stmts
  envTree = EnvTree (M.unions $ map envTreeEnv envtrees)
                    (concatMap envTreeSubtrees envtrees)

proploc :: Prop SourcePos -> SourcePos
proploc (PropId pos _) = pos
proploc (PropString pos _) = pos
proploc (PropNum pos _) = pos

prop :: [(Prop SourcePos, Maybe (Type SourcePos), Expression SourcePos)]
     -> EnvTree
prop [] = empty
prop ((prp, mtype, e):ps) = case mtype of
  Nothing -> unions [expr e, prop ps]
  Just type_ -> unions [EnvTree (M.singleton (proploc prp) [type_]) [], 
                       expr e, prop ps]

expr :: Expression SourcePos -> EnvTree
expr e = case e of
  StringLit{} -> empty
  RegexpLit{} -> empty
  NumLit{} -> empty
  IntLit{} -> empty
  BoolLit{} -> empty
  NullLit{} -> empty
  ArrayLit _ es -> unions $ map expr es
  ObjectLit _ ps -> prop ps
  ThisRef{} -> empty
  VarRef{} -> empty
  DotRef _ e _ -> expr e
  BracketRef _ ec ek -> unions [expr ec, expr ek]
  NewExpr _ ec args -> unions [expr ec, unions $ map expr args]
  PostfixExpr _ _ e -> expr e
  PrefixExpr _ _ e -> expr e
  InfixExpr _ _ e1 e2 -> unions [expr e1, expr e2]
  CondExpr _ e1 e2 e3 -> unions [expr e1, expr e2, expr e3]
  AssignExpr _ _ e1 e2 -> unions [expr e1, expr e2]
  ParenExpr _ e -> expr e
  ListExpr _ es -> unions $ map expr es
  CallExpr pos e ts es -> unions [EnvTree (M.singleton pos ts) [],
                                  unions $ map expr (e:es)]
  FuncExpr pos _ t s -> EnvTree (M.singleton pos [t]) [stmt s]

vardecl :: VarDecl SourcePos -> EnvTree
vardecl (VarDecl _ (Id pos _) type_) = EnvTree (M.singleton pos [type_]) []
vardecl (VarDeclExpr _ (Id pos _) mtype e) = case mtype of
  Nothing -> expr e
  Just type_ -> unions [EnvTree (M.singleton pos [type_]) [], expr e]

catch :: CatchClause SourcePos -> EnvTree
catch (CatchClause _ _ s) = stmt s

caseclause (CaseClause _ e ss) = unions [expr e, unions $ map stmt ss]
caseclause (CaseDefault _ ss) = unions $ map stmt ss
  
forinit NoInit = empty
forinit (VarInit vs) = unions $ map vardecl vs
forinit (ExprInit e) = expr e

forininit :: ForInInit SourcePos -> EnvTree
forininit _ = empty

stmt :: Statement SourcePos -> EnvTree
stmt s = case s of
  BlockStmt _ ss -> buildEnvTree ss
  EmptyStmt _ -> empty
  ExprStmt _ e -> expr e
  IfStmt _ e s1 s2 -> unions [expr e, stmt s1, stmt s2]
  IfSingleStmt _ e s -> unions [expr e, stmt s]
  SwitchStmt _ e cs -> unions ((expr e):(map caseclause cs))
  WhileStmt _ e s -> unions [expr e, stmt s]
  DoWhileStmt _ s e -> unions [stmt s, expr e]
  BreakStmt{} -> empty
  ContinueStmt{} -> empty
  LabelledStmt _ _ s -> stmt s
  ForInStmt _ i e s -> unions [forininit i, expr e, stmt s]
  ForStmt _ i me1 me2 s -> unions [forinit i, maybe empty expr me1,
                                   maybe empty expr me2]
  TryStmt _ s catches fin -> unions [stmt s, unions $ map catch catches,
                                     maybe empty stmt fin]
  ThrowStmt _ e -> expr e
  ReturnStmt _ e -> maybe empty expr e
  VarDeclStmt _ vars -> unions $ map vardecl vars
  TypeStmt{} -> error "NOT DONE YET"  
