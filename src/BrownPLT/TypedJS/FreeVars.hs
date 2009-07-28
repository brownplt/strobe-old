-- |Derived from BrownPLT.JavaScript.Environment.  However, we use this
-- to calculate free variables, not "global variable declarations".
-- TODO: Some of this code is superfluous.
module BrownPLT.TypedJS.FreeVars
  ( freeVars
  ) where

import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.Syntax
import qualified Data.Map as M
import qualified Data.Set as S


-- Intermediate data structure that contains locally declared names and
-- all references to identifers.
data Partial = Partial {
  partialLocals :: Map String SourcePos,
  partialReferences :: Map String SourcePos,
  partialNested :: [Partial]
}


empty :: Partial
empty = Partial M.empty M.empty []


ref :: Id SourcePos -> Partial
ref (Id p v) = Partial M.empty (M.singleton v p) []


decl :: Id SourcePos -> Partial
decl (Id p v) = Partial (M.singleton v p) M.empty []


nest :: Partial -> Partial
nest partial = Partial M.empty M.empty [partial]


-- Combine partial results from the same lexical scope.
unions :: [Partial] -> Partial
unions ps = Partial (M.unions (map partialLocals ps))
                    (M.unions (map partialReferences ps))
                    (concatMap partialNested ps)

lvalue :: LValue SourcePos -> Partial
lvalue lv =  case lv of
  LVar p x -> ref (Id p x)
  LDot _ obj _ -> expr obj
  LBracket _ obj prop -> unions [expr obj, expr prop]


expr :: Expression SourcePos -> Partial
expr e = case e of
  StringLit _ _ -> empty
  RegexpLit _ _ _ _ -> empty
  NumLit _ _ -> empty
  IntLit _ _ -> empty
  BoolLit _ _ -> empty
  NullLit _ -> empty
  ArrayLit _ es -> unions (map expr es)
  ObjectLit _ props -> unions (map (\(_, e') -> expr e') props)
  ThisRef _ -> empty
  AnnotatedVarRef p _ x -> ref (Id p x)
  VarRef _ id -> ref id
  DotRef _ e _ -> expr e
  BracketRef _ e1 e2 -> unions [expr e1, expr e2]
  NewExpr _ e1 es -> unions [expr e1, unions $ map expr es]
  UnaryAssignExpr _ _ lv -> lvalue lv
  PrefixExpr _ _ e -> expr e
  InfixExpr _ _ e1 e2 -> unions [expr e1, expr e2]
  CondExpr _ e1 e2 e3 -> unions [expr e1, expr e2, expr e3]
  AssignExpr _ _ lhs rhs -> unions [lvalue lhs, expr rhs]
  ParenExpr _ e -> expr e
  ListExpr _ es -> unions (map expr es)
  CallExpr _ e _ es -> unions [expr e, unions $ map expr es]
  FuncExpr _ args _ s -> nest $ unions [unions $ map decl args, stmt s]
  PackExpr _ e _ _ -> expr e
  TyAppExpr _ e _ -> expr e


caseClause :: CaseClause SourcePos -> Partial
caseClause cc = case cc of
  CaseClause _ e ss -> unions [expr e, unions $ map stmt ss]
  CaseDefault _ ss -> unions $ map stmt ss


-- TODO: Verify that this is a declaration and not a reference.
catchClause :: CatchClause SourcePos -> Partial
catchClause (CatchClause _ id s) = unions [decl id, stmt s]


varDecl :: VarDecl SourcePos -> Partial
varDecl (VarDecl _ id _) = decl id
varDecl (VarDeclExpr _ id _ e) = unions [decl id, expr e]
varDecl (UnpackDecl _ id _ _ e) = unions [decl id, expr e]

 
forInit :: ForInit SourcePos -> Partial
forInit fi = case fi of
  NoInit -> empty
  VarInit ds -> unions $ map varDecl ds
  ExprInit e -> expr e 


forInInit :: ForInInit SourcePos -> Partial
forInInit (ForInVar id) = decl id
forInInit (ForInNoVar id) = ref id

  
stmt :: Statement SourcePos -> Partial
stmt s = case s of
  BlockStmt _ ss -> unions $ map stmt ss
  EmptyStmt _ -> empty
  ExprStmt _ e -> expr e
  IfStmt _ e s1 s2 -> unions [expr e, stmt s1, stmt s2]
  IfSingleStmt _ e s -> unions [expr e, stmt s]
  SwitchStmt _ e cases -> unions [expr e, unions $ map caseClause cases]
  WhileStmt _ e s -> unions [expr e, stmt s]
  DoWhileStmt _ s e -> unions [stmt s, expr e]
  BreakStmt _ _ -> empty
  ContinueStmt _ _ -> empty
  LabelledStmt _ _ s -> stmt s
  ForInStmt _ fii e s -> unions [forInInit fii, expr e, stmt s]
  ForStmt _ fi  me1 me2 s -> 
    unions [forInit fi, maybe empty expr me1, maybe empty expr me2, stmt s]
  TryStmt _ s catches ms ->
    unions [stmt s, unions $ map catchClause catches, maybe empty stmt ms]
  ThrowStmt _ e -> expr e
  ReturnStmt _ me -> maybe empty expr me
  VarDeclStmt _ decls -> unions $ map varDecl decls
  ExternalFieldStmt _ brand _ e -> unions [ref brand, expr e]
  


-- |The statically-determinate lexical structure of a JavaScript program.
data EnvTree = EnvTree (M.Map String SourcePos) [EnvTree]


-- A 'Partial' specifies identifier references in addition to identifier
-- declarations.  We descend into a 'Partial', pushing enclosing declarations
-- in to remove references to identifiers declared in the enclosing scope.
-- Any referencs to identifiers not declared in either the current or the
-- enclosing scope are local definitions of global variables.
makeEnvTree :: Map String SourcePos -- ^enclosing environment
            -> Partial -- ^local environment and references
            -> (EnvTree,Map String SourcePos) 
            -- ^environment and global definitions
makeEnvTree enclosing (Partial locals references nested) = (tree,globals) where
  nestedResults = map (makeEnvTree (locals `M.union` enclosing)) nested
  tree = EnvTree locals (map fst nestedResults)
  globals' = (references `M.difference` locals) `M.difference` enclosing
  globals = M.unions (globals':(map snd nestedResults))


envTree :: Map String SourcePos -- ^browser/testing environment
        -> [Statement SourcePos] 
        -> (EnvTree,Map String SourcePos)
envTree globals program = makeEnvTree globals (unions $ map stmt program)


freeVars :: [String] -- ^browser/testing environment
         -> [Statement SourcePos]
         -> [(String, SourcePos)]
freeVars globals program = M.toList free
  where (_, free) = makeEnvTree (M.fromList (zip globals (repeat noPos)))
                                (unions (map stmt program))
