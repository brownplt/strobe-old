module TypedJavaScript.ErasedEnvTree
  ( buildErasedEnvTree
  , ErasedEnv
  ) where

import Prelude hiding (catch)
import Data.Tree
import TypedJavaScript.Prelude
import TypedJavaScript.Syntax
import qualified Data.Map as M

type ErasedEnvTree = Tree ErasedEnv

type ErasedEnv = Map SourcePos [Type]


empty :: ErasedEnvTree
empty = Node M.empty []

single :: SourcePos -> Type -> ErasedEnvTree
single loc type_ = multi loc [type_]

multi :: SourcePos -> [Type] -> ErasedEnvTree
multi loc types = Node (M.singleton loc types) []

nest :: ErasedEnvTree -> ErasedEnvTree
nest et = Node M.empty [et]


(+++) :: ErasedEnvTree -> ErasedEnvTree -> ErasedEnvTree
ee1 +++ ee2 =
  Node (M.union (rootLabel ee1) (rootLabel ee2))
       (subForest ee1 ++ subForest ee2)

unions :: [ErasedEnvTree] -> ErasedEnvTree
unions et = foldr (+++) empty et


proploc :: Prop SourcePos -> SourcePos
proploc (PropId pos _) = pos
proploc (PropString pos _) = pos
proploc (PropNum pos _) = pos

prop :: (Prop SourcePos, Maybe (Type), Expression SourcePos)
     -> ErasedEnvTree
prop (prop, mtype, e) = case mtype of
  Nothing -> expr e -- If there is no type annotation, we add nothing
  Just type_ -> expr e +++ single (proploc prop) type_


expr :: Expression SourcePos -> ErasedEnvTree
expr e = case e of
  StringLit{} -> empty
  RegexpLit{} -> empty
  NumLit{} -> empty
  IntLit{} -> empty
  BoolLit{} -> empty
  NullLit{} -> empty
  ArrayLit _ es -> unions $ map expr es
  ObjectLit _ ps -> unions (map prop ps)
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
  CallExpr pos e ts es -> multi pos ts +++ expr e +++ unions (map expr es)
  FuncExpr pos _ t s -> single pos t +++ nest (stmt s)

vardecl :: VarDecl SourcePos -> ErasedEnvTree
vardecl (VarDecl _ (Id pos _) type_) = single pos type_
vardecl (VarDeclExpr _ (Id pos _) mtype e) = case mtype of
  Nothing -> expr e
  Just type_ -> single pos type_ +++ expr e

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
  ForStmt _ i me1 me2 body ->
    forinit i +++ maybe empty expr me1 +++ maybe empty expr me2 +++ stmt body
  TryStmt _ s catches fin -> unions [stmt s, unions $ map catch catches,
                                     maybe empty stmt fin]
  ThrowStmt _ e -> expr e
  ReturnStmt _ e -> maybe empty expr e
  VarDeclStmt _ vars -> unions $ map vardecl vars


buildErasedEnvTree :: [Statement SourcePos] -> ErasedEnvTree
buildErasedEnvTree stmts = 
  complete M.empty $ topLevel +++ unions (map stmt stmts) 
  where complete enclosingEnv (Node env subtrees) =
          let completeEnv = M.union env enclosingEnv
            in Node completeEnv (map (complete completeEnv) subtrees)
        -- The conversion to ANF wraps the program in 0-arity function.
        -- The location of this function is (noPos "Intraprocedural.hs").
        -- If the filename of the Typed JavaScript program is 
        -- Intraprocedural.hs, this may be problematic.
        topLevel = single (initialPos "Intraprocedural.hs")
                          (TFunc [TObject True [], TSequence [] Nothing] 
                                 (TId "undefined")
                                 LPNone)
