-- |Pretty-printing Typed JavaScript.
module TypedJavaScript.PrettyPrint
  ( showSp
  , renderType
  , renderStatements
  ) where

import Prelude hiding (id)
import Text.PrettyPrint.HughesPJ
import TypedJavaScript.Syntax
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


typeConstraint :: TypeConstraint -> Doc
typeConstraint tc = case tc of
  TCSubtype v t2 ->  text v <+> text "<:" <+> type_ t2


renderType :: Type -> String
renderType t = render (type_ t)


renderStatements :: [Statement a] -> String
renderStatements ss = render $ vcat (map (\s -> stmt s <> semi) ss)


type_ :: Type -> Doc
type_ t = case t of
  TPrototype str ->
    text ("TPrototype " ++ str)
  TFunc ptype (this:arguments:args) ret _ -> 
    brackets (type_ this) <+> commas (map arg args) <> varargDoc <+> 
    
    (if (isJust ptype) then text "~~>" else text "->") <+> type_ ret
      where arg t' = case t' of
              TFunc{} -> parens (type_ t')
              otherwise -> type_ t'
            varargDoc = case arguments of
              TSequence _ (Just t') -> comma <+> arg t' <+> text "..."
              -- We ignore the case where arguments is not a TSequence.
              otherwise -> empty 
  TEnvId s -> text "*" <> text s <> text "*"
  TSequence ts opt -> brackets $ (commas (map type_ ts)) <> optional
    where optional = case opt of
            Nothing -> empty
            Just t -> text "," <+> type_ t <+> text "..."
  TApp s ts -> text s <> text "<" <> commas (map type_ ts) <> text ">"
  TAny -> text "any"
  TRec id t -> hang (text "rec" <+> text id <+> text ".") 2 (type_ t)
  TObject hasSlack isOpen fields -> 
   braces $ open <> nest 2 (commas (map field fields) <> s)
    where fieldFull (id, t') = text id <+> text "::" <+> type_ t'
          fieldShrt (id, x)  = text id <+> text "::" <+> text x <> text "***"
          field (id, t') = let tfield = render $ type_ t' in
            if length tfield > 40 
               then fieldShrt (id, filter ((/=) '\n') $ take 40 tfield)
               else fieldFull (id, t')
          open = text $ if isOpen then "(open)" else ""                  
          s = case hasSlack of
                True -> text ", ..."
                False -> empty
  TUnion ts -> text "U" <+> parens (commas (map type_ ts'))
                 where ts' = if elem undefType ts
                               then (undefType:(delete undefType ts))
                               else ts 
                       undefType = TId "undefined"
  TId v -> text v
  TForall ids cs t' ->
    text "forall" <+> (commas (map text ids)) <+> constraintsDoc <+> 
    text "." <+> type_ t'
      where constraintsDoc = case cs of
              [] -> empty
              otherwise -> text ":" <+> commas (map typeConstraint cs)
  TIterator i -> text "TIterator" <+> text i
  TProperty i -> text "TProperty" <+> text i


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


topLevelStatement :: ToplevelStatement a -> Doc
topLevelStatement s = case s of
  TypeStmt _ v t -> 
    text "type " <+> id v <+> text " :: " <+> type_ t
  ExternalStmt _ v t ->
    text "external " <+> id v <+> text " :: " <+> type_ t


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
  PrefixInc -> "++"
  PrefixDec -> "--"
  PrefixLNot -> "!"
  PrefixBNot -> "~"
  PrefixPlus -> "+"
  PrefixMinus -> "-"
  PrefixVoid -> "void"
  PrefixTypeof -> "typeof"
  PrefixDelete -> "delete"


postfix :: PostfixOp -> Doc
postfix op = text $ case op of
  PostfixInc -> "++"
  PostfixDec -> "--"


assignOp :: AssignOp -> Doc
assignOp op = text $ case op of
	  OpAssign -> "->"
	  OpAssignAdd -> "+->"
	  OpAssignSub -> "-->"
	  OpAssignMul -> "*->"
	  OpAssignDiv -> "/->"
	  OpAssignMod -> "%->"
	  OpAssignLShift -> "<<->"
	  OpAssignSpRShift -> ">>->"
	  OpAssignZfRShift -> ">>>->"
	  OpAssignBAnd -> "&->"
	  OpAssignBXor -> "^->"
	  OpAssignBOr -> "|->"


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
    braces (hsep (punctuate comma (map id' xs))) where
      id' (n,mt,v) = prop n <+> idMaybe mt <+> colon <+> expr v
      idMaybe mt = case mt of
        (Just t) -> text "::" <+> type_ t
        Nothing  -> empty
  ThisRef _ -> text "this"
  VarRef _ v -> id v
  DotRef _ e v ->
    expr e <> text "." <> id v
  BracketRef _ container key ->
    expr container <> brackets (expr key)
  NewExpr _ constr args -> 
    text "new" <+> expr constr <> (parens $ commas $ map expr args)
  PrefixExpr _ op e ->
    prefix op <+> expr e
  PostfixExpr _ op e ->
    expr e <+> postfix op
  InfixExpr _ op left right -> 
    expr left <+> infix_ op <+> expr right
  CondExpr _ test cons alt ->
    expr test <+> text "?" <+> expr cons <+> colon <+> expr alt
  AssignExpr _ op l r ->
    expr l <+> assignOp op <+> expr r
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
