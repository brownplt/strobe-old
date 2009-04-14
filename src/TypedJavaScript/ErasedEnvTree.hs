module TypedJavaScript.ErasedEnvTree
  ( buildErasedEnvTree
  , ErasedEnv
  ) where


import Prelude hiding (catch)
import Data.Tree
import TypedJavaScript.Prelude
import TypedJavaScript.Syntax
import TypedJavaScript.PrettyPrint ()
import qualified Data.Map as M

type ErasedEnvTree = Tree ErasedEnv

type ErasedEnv = Map SourcePos [Type SourcePos]

empty :: ErasedEnvTree
empty = Node M.empty []

unions :: [ErasedEnvTree] -> ErasedEnvTree
unions et = Node (M.unionsWith 
                    (\t1 t2 -> error $ printf "Overlapping %s, %s" 
                                              (show t1) (show t2))
                    (map rootLabel et))
                 (concatMap subForest et)

buildErasedEnvTree :: [Statement SourcePos] -> ErasedEnvTree
buildErasedEnvTree stmts = complete M.empty $ unions (map stmt stmts) where
  complete enclosingEnv (Node env subtrees) =
    let completeEnv = M.union env enclosingEnv -- left-biased, shadows correctly
      in Node completeEnv (map (complete completeEnv) subtrees)

proploc :: Prop SourcePos -> SourcePos
proploc (PropId pos _) = pos
proploc (PropString pos _) = pos
proploc (PropNum pos _) = pos

prop :: [(Prop SourcePos, Maybe (Type SourcePos), Expression SourcePos)]
     -> ErasedEnvTree
prop [] = empty
prop ((prp, mtype, e):ps) = case mtype of
  Nothing -> unions [expr e, prop ps]
  Just type_ -> unions [Node (M.singleton (proploc prp) [type_]) [], 
                       expr e, prop ps]

expr :: Expression SourcePos -> ErasedEnvTree
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
  CallExpr pos e ts es -> unions [Node (M.singleton pos ts) [],
                                  unions $ map expr (e:es)]
  FuncExpr pos _ t s -> Node (M.singleton pos [t]) [stmt s]

vardecl :: VarDecl SourcePos -> ErasedEnvTree
vardecl (VarDecl _ (Id pos _) type_) = 
  Node (M.singleton pos [type_]) []
vardecl (VarDeclExpr _ (Id pos _) mtype e) = case mtype of
  Nothing -> expr e
  Just type_ -> unions [Node (M.singleton pos [type_]) [], expr e]

catch :: CatchClause SourcePos -> ErasedEnvTree
catch (CatchClause _ _ s) = stmt s

caseclause (CaseClause _ e ss) = unions [expr e, unions $ map stmt ss]
caseclause (CaseDefault _ ss) = unions $ map stmt ss
  
forinit NoInit = empty
forinit (VarInit vs) = unions $ map vardecl vs
forinit (ExprInit e) = expr e

forininit :: ForInInit SourcePos -> ErasedEnvTree
forininit _ = empty

stmt :: Statement SourcePos -> ErasedEnvTree
stmt s = case s of
  BlockStmt _ ss -> unions (map stmt ss)
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

