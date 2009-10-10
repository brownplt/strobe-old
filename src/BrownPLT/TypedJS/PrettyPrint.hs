-- |Pretty-printing Typed JavaScript.
module BrownPLT.TypedJS.PrettyPrint
  ( renderType
  , prettyType
  , prettyTopLevel
  , renderStatements
  , renderExpr
  ) where

import Prelude hiding (id)
import Text.PrettyPrint.HughesPJ
import BrownPLT.TypedJS.Syntax
import BrownPLT.JavaScript.Analysis.ANFPrettyPrint (prettyLit)
import BrownPLT.TypedJS.Prelude

-- Displays the statement in { ... }, unless it already is in a block.
inBlock :: Statement a -> Doc
inBlock s@(BlockStmt _ _) = stmt s
inBlock s = lbrace $$ nest 2 (stmt s) $$ rbrace


-- Displays the expression in ( ... ), unless it already is in parens.
inParens:: Expression a -> Doc
inParens e@(ParenExpr _ _) = expr e
inParens e                 = parens (expr e)


commas :: [Doc] -> Doc
commas ds = sep (punctuate comma ds)


hangBraces :: Doc -> Doc
hangBraces doc = lbrace $$ (nest 2 doc) $$ rbrace


renderExpr :: Expression a -> String
renderExpr e = render (expr e)


prettyType :: Type -> Doc
prettyType = type_


renderType :: Type -> String
renderType t = render (type_ t)


renderStatements :: [Statement a] -> String
renderStatements ss = render $ vcat (map (\s -> stmt s <> semi) ss)


field :: (String, Bool, Type) -> Doc
field (x, True, t) = text "readonly" <+> text x <+> text "::" <+> type_ t
field (x, False, t) = text x <+> text "::" <+> type_ t 

argType :: ArgType -> Doc
argType (ArgType args Nothing) = 
  commas (map type_ args)
argType (ArgType args (Just opt)) = 
  commas (map type_ args) <> comma <+> type_ opt <+> text "..."

type_ :: Type -> Doc
type_ t = case t of
  TArguments at -> argType at
  TArrow this at r -> argType at <+> text "->" <+> type_ r
  TApp s [] -> text s
  TApp s ts -> text s <> text "<" <> commas (map type_ ts) <> text ">"
  TAny -> text "any"
  TObject "Object" [] fields -> braces (nest 2 (commas (map field fields)))
  TObject brand [] fields ->
    text brand <> braces (nest 2 (commas (map field fields)))
  TObject brand tyArgs fields ->
    text brand <> brackets (commas (map type_ tyArgs)) <>
    braces (nest 2 (commas (map field fields)))
  TUnion t1 t2 -> text "U" <> parens (type_ t1 <> comma <+> type_ t2)
  TIx n -> text (show n)
  TExists t -> text "exists ." <+> type_ t
  TId x -> text x
  TForall t -> text "forall ." <+> type_ t
  TNamedForall x t -> text "forall" <+> text x <+> text "." <+> type_ t
  TIntersect t1 t2 -> parens (type_ t1) <> text " ^ " <> parens (type_ t2)
  TConstr brand args initTy objTy -> commas (map type_ args) <+> text "~~>" <+>
    type_ objTy


id :: Id a -> Doc
id (Id _ s) = text s


forInit :: ForInit a -> Doc
forInit fi = case fi of
  NoInit -> empty
  VarInit decls -> text "var" <+> commas (map varDecl decls)
  ExprInit e -> expr e


forInInit :: ForInInit a -> Doc
forInInit fii = case fii of
  ForInVar v -> text "var" <+> id v
  ForInNoVar v -> id v


caseClause :: CaseClause a -> Doc
caseClause cc = case cc of
  CaseClause _ e ss -> 
    text "case" $+$ expr e <+> colon $+$ (nest 2 $ vcat (map stmt ss))
  CaseDefault _ ss ->
    text "default:" $+$ (nest 2 $ vcat (map stmt ss))


catchClause :: CatchClause a -> Doc
catchClause cc = case cc of
  CatchClause _ v s -> text "catch" <+> parens (id v) <+> inBlock s


varDecl :: VarDecl a -> Doc
varDecl decl = case decl of
  VarDecl _ v t ->
    id v <+> text "::" <+> type_ t
  VarDeclExpr _ v Nothing e ->
    id v <+> equals <+> expr e
  VarDeclExpr _ v (Just t) e -> 
    id v <+> text "::" <+> type_ t <+> equals <+> expr e
  UnpackDecl _ x tVars e -> 
    id x <+> text ":: unpack " <+> hsep (map text tVars) <+> equals <+> expr e


stmt :: Statement a -> Doc
stmt s = case s of
  BlockStmt _ ss -> hangBraces (vcat (map (\s -> stmt s <> semi) ss))
  EmptyStmt _ -> semi
  ExprStmt _ e -> expr e
  IfSingleStmt _ test cons -> 
    text "if" <+> inParens test $$ hangBraces (stmt cons)
  IfStmt _ test cons alt ->
    text "if" <+> inParens test $$ 
    hangBraces (stmt cons) $+$ 
    text "else" $$ hangBraces (stmt alt)
  SwitchStmt _ e cases -> 
    text "switch" <+> inParens e $$ 
    hangBraces (vcat $ map caseClause cases)
  WhileStmt _ test body ->
    text "while" <+> inParens test $$ hangBraces (stmt body)
  ReturnStmt _ Nothing -> text "return"
  ReturnStmt _ (Just e) -> text "return" <+> (expr e)
  DoWhileStmt _ s e -> 
    text "do" <> 
    hangBraces (stmt s) <>
    text "while" <+> inParens e
  BreakStmt _ Nothing -> text "break"
  BreakStmt _ (Just l) -> text "break" <+> id l
  ContinueStmt _ Nothing -> text "continue"
  ContinueStmt _ (Just l) -> text "continue" <+> id l
  LabelledStmt _ l s -> id l <> colon $$ stmt s
  ForInStmt p i e s -> 
    text "for" <+> parens (forInInit i <+> text "in" <+> expr e) <> stmt s
  ForStmt _ init incr test body ->
    text "for" <+> 
    parens (forInit init <> semi <+> yExpr incr <> semi <+> yExpr test) $$ 
    inBlock body
  TryStmt _ body catches finally ->
    text "try" <> inBlock body $+$ vcat (map catchClause catches) $+$ finallyDoc
      where finallyDoc = case finally of
              Nothing -> empty
              Just s -> inBlock s
  ThrowStmt _ e -> text "throw" <+> expr e
  VarDeclStmt _ decls ->
    text "var" <+> commas (map varDecl decls) 


prop :: Prop a -> Doc
prop p = case p of
  PropId _ v ->  id v
  PropString _ str -> doubleQuotes (text (jsEscape str))
  PropNum _ n -> text (show n)


infix_ :: InfixOp -> Doc
infix_ op = text $ case op of
  OpMul -> "*"
  OpDiv -> "/"
  OpMod -> "%" 
  OpAdd -> "+" 
  OpSub -> "-"
  OpLShift -> "<<"
  OpSpRShift -> ">>"
  OpZfRShift -> ">>>"
  OpLT -> "<"
  OpLEq -> "<="
  OpGT -> ">"
  OpGEq -> ">="
  OpIn -> "in"
  OpInstanceof -> "instanceof"
  OpEq -> "=="
  OpNEq -> "!="
  OpStrictEq -> "==="
  OpStrictNEq -> "!=="
  OpBAnd -> "&"
  OpBXor -> "^"
  OpBOr -> "|"
  OpLAnd -> "&&"
  OpLOr -> "||"


prefix :: PrefixOp -> Doc
prefix op = text $ case op of
  PrefixLNot -> "!"
  PrefixBNot -> "~"
  PrefixPlus -> "+"
  PrefixMinus -> "-"
  PrefixVoid -> "void"
  PrefixTypeof -> "typeof"
  PrefixDelete -> "delete"


assignOp :: AssignOp -> Doc
assignOp op = text $ case op of
	  OpAssign -> "="
	  OpAssignAdd -> "+="
	  OpAssignSub -> "-="
	  OpAssignMul -> "*="
	  OpAssignDiv -> "/="
	  OpAssignMod -> "%="
	  OpAssignLShift -> "<<="
	  OpAssignSpRShift -> ">>="
	  OpAssignZfRShift -> ">>>="
	  OpAssignBAnd -> "&="
	  OpAssignBXor -> "^="
	  OpAssignBOr -> "|="


-- Based on:
--   http://developer.mozilla.org/en/docs/Core_JavaScript_1.5_Guide:Literals
jsEscape:: String -> String
jsEscape "" = ""
jsEscape (ch:chs) = (sel ch) ++ jsEscape chs where
    sel '\b' = "\\b"
    sel '\f' = "\\f"
    sel '\n' = "\\n"
    sel '\r' = "\\r"
    sel '\t' = "\\t"
    sel '\v' = "\\v"
    sel '\'' = "\\'"
    sel '\"' = "\\\""
    sel '\\' = "\\\\"
    sel x    = [x]
    -- We don't have to do anything about \X, \x and \u escape sequences.


yExpr :: Maybe (Expression a) -> Doc
yExpr Nothing = empty
yExpr (Just e) = expr e


lvalue :: LValue a -> Doc
lvalue (LVar _ x) = text x
lvalue (LDot _ e x) = expr e <> text "." <> text x
lvalue (LBracket _ e1 e2) = expr e1 <> brackets (expr e2)


expr :: Expression a -> Doc
expr e = case e of
  StringLit _ str -> doubleQuotes (text (jsEscape str))
  RegexpLit _ re global ci ->
    text "/" <> text re <> text "/" <> g <> i where
      g = if global then text "g" else empty
      i = if ci then text "i" else empty
  NumLit _ n ->  text (show n)
  IntLit _ n ->  text (show n)
  BoolLit _ True -> text "true"
  BoolLit _ False -> text "false"
  NullLit _ -> text "null"
  ArrayLit _ es -> brackets (commas (map expr es))
  ObjectLit _ xs -> 
    braces (hsep (punctuate comma (map prop_ xs)))
      where prop_ (n, v) = prop n <+> colon <+> expr v
  ThisRef _ -> text "this"
  VarRef _ v -> id v
  AnnotatedVarRef _ rt x -> 
    text x <> braces (text (show rt))
  DotRef _ e v ->
    expr e <> text "." <> id v
  BracketRef _ container key ->
    expr container <> brackets (expr key)
  NewExpr _ constr args -> 
    text "new" <+> expr constr <> (parens $ commas $ map expr args)
  PrefixExpr _ op e ->
    prefix op <+> expr e
  UnaryAssignExpr _ op e' -> case op of
    PrefixInc -> text "++" <> lvalue e'
    PrefixDec -> text "--" <> lvalue e'
    PostfixInc -> lvalue e' <> text "++"
    PostfixDec -> lvalue e' <> text "--"
  InfixExpr _ op left right -> 
    expr left <+> infix_ op <+> expr right
  CondExpr _ test cons alt ->
    expr test <+> text "?" <+> expr cons <+> colon <+> expr alt
  AssignExpr _ op l r ->
    lvalue l <+> assignOp op <+> expr r
  ParenExpr _ e ->
    parens (expr e)
  ListExpr _ es -> commas (map expr es)
  CallExpr _ f [] args ->
    expr f <> parens (commas $ map expr args)
  CallExpr _ f types args -> 
    expr f <> text "@" <> (brackets $ commas (map type_ types))
           <> (parens $ commas $ map expr args)
  FuncExpr _ args t body ->
    text "function" <+> parens (commas $ map id args) <+> text "::" 
                    <+> type_ t $$ inBlock body
  PackExpr _ e cTy ty -> text "pack" <+> type_ cTy <+> type_ ty <+>
    text "in" <+> expr e
  TyAppExpr _ e ty -> expr e <> text "@" <> brackets (type_ ty)


topLevel :: TopLevel SourcePos -> Doc
topLevel tl = case tl of
  TopLevelStmt s -> stmt s
  ExternalFieldStmt _ brand field e ->
    id brand <> text ".prototype." <> id field <+> text "=" <+> expr e
  ConstructorStmt p brand args ty asgns body ->
    text "constructor" <+> text brand <+> parens (commas $ map text args) <+>
    text "::" <+> type_ ty <+> (stmt $ constrBodyStmt p asgns body)
  ImportStmt _ name isAssumed ty ->
    text "import" <+> assumed <> id name <+> text "::" <+> type_ ty
      where assumed = case isAssumed of
              True -> text "assumed " 
              False -> empty
  ImportConstrStmt _ name isAssumed ty ->
    text "import" <+> assumed <> text "constructor" <+> id name <+> text "::" 
    <+> type_ ty
      where assumed = case isAssumed of
              True -> text "assumed " 
              False -> empty


prettyTopLevel :: [TopLevel SourcePos] -> String
prettyTopLevel tls = render (vcat $ map topLevel tls)
