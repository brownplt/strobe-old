module BrownPLT.TypedJS.Parser
  ( parseScript
  , parseExpression
  , parseType
  , parseType'
  , parseString
  , parseFuncExpr
  , parseScriptFromString
  , emptyParsedJavaScript
  , ParsedStatement
  , ParsedExpression
  , parseJavaScriptFromFile
  , parseSimpleExpr'
  , parseBlockStmt
  , parseStatement
  , StatementParser
  , ExpressionParser
  , assignExpr
  , parseToplevel, parseToplevels
  , parseTypedJavaScript
  ) where

import BrownPLT.TypedJS.TypeTheory (undefType)
import qualified BrownPLT.JavaScript.Analysis.ANF as ANF
import BrownPLT.TypedJS.Lexer hiding (identifier)
import qualified BrownPLT.TypedJS.Lexer as Lexer
import BrownPLT.TypedJS.Syntax
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Control.Monad(liftM,liftM2)
import Control.Monad.Trans (MonadIO,liftIO)
import Numeric(readDec,readOct,readHex)
import Data.Char(chr)
import Data.Char
import Data.List
import BrownPLT.TypedJS.TypeTheory (closeType)
 
-- We parameterize the parse tree over source-locations.
type ParsedStatement = Statement SourcePos
type ParsedExpression = Expression SourcePos
type ParsedType = Type
type ParsedToplevel = ToplevelStatement SourcePos
type MaybeParsedType = Maybe (Type)

-- These parsers can store some arbitrary state
type StatementParser state = CharParser state ParsedStatement
type ExpressionParser state = CharParser state ParsedExpression
type TypeParser state = CharParser state ParsedType
type MaybeTypeParser state = CharParser state MaybeParsedType
type ToplevelParser state = CharParser state ParsedToplevel

identifier =
  liftM2 Id getPosition Lexer.identifier

{- The syntax for types is:

 type ::= identifier
        | any
        | 'literal
        | type?
        | '[' type ']' type [,*] -> type?     ; explicit this
        | '[' type ']' type [,+] ... -> type? ; explicit this
        | type [,*] -> type?
        | type [,+] ... -> type?
        | constr
        | constr '[' type [,*] ']'
        | forall identifier+ . type
        | ( type )
        | identifier:{ [readonly] id: type' [,*] }
        | identifier: ; object without additional field constraints
        | { [readonly] id: type' [,*] } ; implicitly branded Object

Disambiguation:

 type ::= forall identifier+ . type
        | exists id+ . type
        | forall id+ . type
        | rec identifier . type
        | type_fn

 type_fn ::= type' [,*] -> type?
           | type' [,+] ... -> type?
           | '[' type ']' type' [,*] -> type?
           | '[' type ']' type' [,+] ... -> type?
           | type'

 type' ::= type''?
         | type''

 type'' ::= identifier
          | ( type )
          | identifier:{ [readonly] id: type' [,*] }
          | identifier:
          | { [readonly] id: type' [,*] } ; implicitly branded Object
          | constr
          | constr '[' type [,*] ']'
          | 'literal
          | any

 -} 

type_ :: CharParser st (Type)
type_ = do
  let exists = do
        reserved "exists"
        xs <- many1 Lexer.identifier
        reservedOp "."
        t <- type_
        return (foldr (\x t -> TExists (closeType x t)) t xs)
  let forall = do
        reserved "forall"
        xs <- many1 Lexer.identifier
        reservedOp "."
        t <- type_
        return (foldr (\x t -> TNamedForall x t) t xs)
  exists <|> forall <|> type_fn


type_fn :: CharParser st (Type)
type_fn = do
  p <- getPosition
  let globalThis = TObject "Window" []
  ts <- type_' `sepBy` comma
  let thisType = TObject "Window" []
  let func = do
        reservedOp "->"
        r <- type_
        return (TArrow (TObject "Window" []) (ArgType ts Nothing) r)
  case ts of
    []  -> func -- function of zero arguments
    [t] -> func <|> (return t)
    ts  -> func

type_' :: CharParser st (Type)
type_' = do
  t <- type_''
  let nullable = do
        reservedOp "?"
        return (TUnion t undefType)
  nullable <|> (return t) <?> "possibly nullable type"

type_'' :: CharParser st (Type)
type_'' = do
  let union = do 
        reservedOp "U";
        elts <- parens (type_'' `sepBy1` comma)
        case elts of
          [t] -> return t
          (t:ts) -> return (foldr TUnion t ts)
  let any = do
        reserved "any"
        return TAny
  let noDupFields fields
        | length (nub $ map (\(x, _, _) -> x) fields) == 
          length fields = return fields
        | otherwise = fail "duplicate fields in an object type specification"
  let object = do
        fields <- braces (field `sepBy` comma)
        fields <- noDupFields fields
        return (TObject "Object" fields)
  -- free type variables, type constructors and objects
  let app constr = do
        args <- (brackets $ type_' `sepBy` comma) <?> "type application"
        return (TApp constr args)
  let brandedObject brand = do
        colon
        let withFields = do
              fields <- braces (field `sepBy` comma)
              fields <- noDupFields fields
              return (TObject brand fields)
        withFields <|> (return $ TObject brand [])
  -- If the first letter is upper-case, an unapplied identifier is a nullary
  -- type constructor.  If it is lower-case, it is a free type variable.
  -- Therefore, basic types such as integers, booleans, etc. must be "Int",
  -- "Bool", etc.  Furthermore, if we support type aliases, they must begin
  -- with an upper-case letter too.
  let other = do
        id <- Lexer.identifier
        case isUpper (head id) of
          True -> (app id) <|> (brandedObject id) <|> (return $ TApp id [])
          False -> (app id) <|> (brandedObject id) <|> (return $ TId id)
    in (parens type_) <|> any <|> (try union) <|> object <|> other


field :: CharParser st (String, Bool, Type)
field = do
  ro <- (reserved "readonly" >> return True) <|> (return False)
  name <- Lexer.identifier
  reservedOp "::"
  t <- type_'
  return (name, ro, t)
 
parseType' :: CharParser st Type
parseType' = type_
 
parseType :: TypeParser st
parseType = do
  reservedOp "::" <?> "type annotation (:: followed by a type)"
  t <- type_
  return t

parseMaybeType :: MaybeTypeParser st
parseMaybeType = do
  (do t <- parseType
      return (Just t)) <|> (return Nothing)

-- ----------------------------------------------------------------------------
-- Statements

externalFieldStmt :: StatementParser st
externalFieldStmt = do
  p <- getPosition
  -- avoid ambiguity with ExprStmt.
  brand <- try $ do brand <- identifier
                    reservedOp "."
                    reserved "prototype"
                    return brand
  reservedOp "."
  field <- identifier
  reservedOp "="
  e <- expr 
  return (ExternalFieldStmt p brand field e)

-- Keep in mind that Token.reserved parsers (exported from the lexer) do not
-- consume any input on failure.  Note that all statements (expect for labelled
-- and expression statements) begin with a reserved-word.  If we fail to parse
-- this reserved-word, no input is consumed.  Hence, we can have the massive or
-- block that is parseExpression.  Note that if the reserved-word is parsed, it 
-- must be whatever statement the reserved-word indicates.  If we fail after the
-- reserved-word, we truly have a syntax error.  Since input has been consumed,
-- <|> will not try its alternate in parseExpression, and we will fail.
parseIfStmt:: StatementParser st  
parseIfStmt = do
  pos <- getPosition
  reserved "if"
  test <- parseParenExpr <?> "parenthesized test-expression in if statement"
  consequent <- parseStatement <?> "true-branch of if statement"
  optional semi -- TODO: in spec?
  ((do reserved "else"
       alternate <- parseStatement
       return (IfStmt pos test consequent alternate))
    <|> return (IfSingleStmt pos test consequent))

parseSwitchStmt:: StatementParser st
parseSwitchStmt =
  let parseDefault = do
        pos <- getPosition
        reserved "default"
        colon
        statements <- many parseStatement
        return (CaseDefault pos statements)
      parseCase = do
         pos <- getPosition
         reserved "case"
         condition <- parseListExpr
         colon
         actions <- many parseStatement
         return (CaseClause pos condition actions)
    in do pos <- getPosition
          reserved "switch"
          test <- parseParenExpr
          clauses <- braces $ many $ parseDefault <|> parseCase
          return (SwitchStmt pos test clauses)

parseWhileStmt:: StatementParser st
parseWhileStmt = do
  pos <- getPosition
  reserved "while"
  test <- parseParenExpr <?> "parenthesized test-expression in while loop"
  body <- parseStatement
  return (WhileStmt pos test body)

parseDoWhileStmt:: StatementParser st
parseDoWhileStmt = do
  pos <- getPosition
  reserved "do"
  body <- parseBlockStmt
  reserved "while" <?> "while at the end of a do block"
  test <- parseParenExpr <?> "parenthesized test-expression in do loop"
  optional semi
  return (DoWhileStmt pos body test)

parseContinueStmt:: StatementParser st
parseContinueStmt = do
  pos <- getPosition
  reserved "continue"
  pos' <- getPosition
  -- Ensure that the identifier is on the same line as 'continue.'
  id <- (if (sourceLine pos == sourceLine pos')
           then (liftM Just identifier) <|> (return Nothing)
           else return Nothing)
  return (ContinueStmt pos id)

parseBreakStmt:: StatementParser st
parseBreakStmt = do
  pos <- getPosition
  reserved "break"
  pos' <- getPosition
  -- Ensure that the identifier is on the same line as 'break.'
  id <- (if (sourceLine pos == sourceLine pos')
           then (liftM Just identifier) <|> (return Nothing)
           else return Nothing)
  optional semi           
  return (BreakStmt pos id)

parseBlockStmt:: StatementParser st
parseBlockStmt = do
  pos <- getPosition
  statements <- braces (many parseStatement)
  return (BlockStmt pos statements)

parseEmptyStmt:: StatementParser st 
parseEmptyStmt = do
  pos <- getPosition
  semi
  return (EmptyStmt pos)

parseLabelledStmt:: StatementParser st
parseLabelledStmt = do
  pos <- getPosition
  -- Lookahead for the colon.  If we don't see it, we are parsing an identifier
  -- for an expression statement.
  label <- try (do label <- identifier
                   colon
                   return label)
  statement <- parseStatement
  return (LabelledStmt pos label statement)

parseExpressionStmt:: StatementParser st
parseExpressionStmt = do
  pos <- getPosition
  expr <- parseListExpr -- TODO: spec 12.4?
  optional semi
  return (ExprStmt pos expr)

parseForInStmt:: StatementParser st
parseForInStmt =
  let parseInit = (do reserved "var"
                      id <- identifier
                      return (ForInVar id)) <|>
                  (do id <- identifier
                      return (ForInNoVar id))
    in do pos <- getPosition
          -- Lookahead, so that we don't clash with parseForStmt
          (init,expr) <- try (do reserved "for"
                                 parens (do init <- parseInit
                                            reserved "in"
                                            expr <- parseExpression
                                            return (init,expr)))
          body <- parseStatement
          return (ForInStmt pos init expr body) 

parseForStmt:: StatementParser st
parseForStmt =
  let parseInit =
        (reserved "var" >> liftM VarInit (varDecl `sepBy` comma)) <|>
        (liftM ExprInit parseListExpr) <|>
        (return NoInit)
    in do pos <- getPosition
          reserved "for"
          reservedOp "("
          init <- parseInit
          semi
          test <- (liftM Just parseListExpr) <|> (return Nothing)
          semi
          iter <- (liftM Just parseListExpr) <|> (return Nothing)
          reservedOp ")" <?> "closing paren"
          stmt <- parseStatement
          return (ForStmt pos init test iter stmt)

parseTryStmt:: StatementParser st
parseTryStmt =
  let parseCatchClause = do
        pos <- getPosition
        reserved "catch"
        id <- parens identifier
        stmt <- parseStatement
        return (CatchClause pos id stmt)
    in do reserved "try"
          pos <- getPosition
          guarded <- parseStatement
          catches <- many parseCatchClause
          finally <- (reserved "finally" >> liftM Just parseStatement) 
                      <|> (return Nothing)
          return (TryStmt pos guarded catches finally)

parseThrowStmt:: StatementParser st
parseThrowStmt = do
  pos <- getPosition
  reserved "throw"
  expr <- parseExpression
  optional semi
  return (ThrowStmt pos expr)

parseReturnStmt:: StatementParser st
parseReturnStmt = do
  pos <- getPosition
  reserved "return"
  expr <- (liftM Just parseListExpr) <|> (return Nothing)
  optional semi
  return (ReturnStmt pos expr)


-- varDecl ::= id = expr
--           | id :: type = expr
--           | id :: type
--           | id :: unpack id . type = expr
varDecl ::  CharParser st (VarDecl SourcePos)
varDecl = do
  p <- getPosition
  id <- identifier
  let noAnnotation = do
        reservedOp "="
        expr <- parseExpression
        return (VarDeclExpr p id Nothing expr)
  let elimExistential = do
        reserved "unpack"
        x <- Lexer.identifier
        reservedOp "."
        t <- type_
        reservedOp "="
        e <- parseExpression
        return (UnpackDecl p id x t e)
  let withExpr t = do
        reservedOp "="
        e <- parseExpression
        return (VarDeclExpr p id (Just t) e)
  let maybeWithExpr = do
        t <- type_
        withExpr t <|> return (VarDecl p id t)
  let withAnnotation = do
        reservedOp "::"
        elimExistential <|> maybeWithExpr
  noAnnotation <|> withAnnotation

 
varDeclStmt:: StatementParser st
varDeclStmt = do 
  pos <- getPosition
  reserved "var"
  decls <- varDecl `sepBy` comma
  optional semi
  return (VarDeclStmt pos decls)

parseFunctionStmt:: StatementParser st
parseFunctionStmt = do
  name <- try (reserved "function" >> identifier) -- ambiguity with FuncExpr
  pos <- getPosition
  args <- parens (identifier `sepBy` comma)
  functype <- parseType <?> "function type annotation"
  body <- parseBlockStmt
  --transform a function statement into an assignment and a funcexpr
  return (VarDeclStmt pos [VarDeclExpr pos name (Just functype) 
                                       (FuncExpr pos args functype body)])

--same as function stmt
{-parseConstructorStmt :: StatementParser st
parseConstructorStmt = do
  reserved "constructor"
  name <- identifier
  pos <- getPosition
  args <- parens (identifier `sepBy` comma)
  constrtype <- parseType <?> "constructor type annotation"
  body <- parseBlockStmt <?> "constructor body in { ... }"
  return (VarDeclStmt pos [VarDeclExpr pos name (Just constrtype) 
                                       (FuncExpr pos args constrtype body)])
-}

{-
parseTypeStmt :: StatementParser st
parseTypeStmt = do
  pos <- getPosition
  reserved "type"
  id <- identifier
  thetype <- parseType
  semi
  return (TypeStmt pos id thetype) -}
               
parseStatement:: StatementParser st
parseStatement = parseIfStmt <|> parseSwitchStmt <|> parseWhileStmt 
  <|> parseDoWhileStmt <|> parseContinueStmt <|> parseBreakStmt 
  <|> parseBlockStmt <|> parseEmptyStmt <|> parseForInStmt <|> parseForStmt
  <|> parseTryStmt <|> parseThrowStmt <|> parseReturnStmt
  <|> varDeclStmt  <|> parseFunctionStmt
  -- added for tJS
  -- <|> parseConstructorStmt 
  -- order matters to handle ambiguity
  <|> externalFieldStmt
  <|> parseLabelledStmt
  <|> parseExpressionStmt
  <?> "statement"

--}}}

--{{{ Expressions

-- References used to construct this stuff:
-- + http://developer.mozilla.org/en/docs/
--     Core_JavaScript_1.5_Reference:Operators:Operator_Precedence
-- + http://www.mozilla.org/js/language/grammar14.html
--
-- Aren't expression tables nice?  Well, we can't quite use them, because of 
-- JavaScript's ternary (?:) operator.  We have to use two expression tables.
-- We use one expression table for the assignment operators that bind looser 
-- than ?: (assignTable).  The terms of assignTable are ternary expVarDeclStmt a [VarDecl a]ressions 
-- (parseTernaryExpr).  parseTernaryExpr left-factors the left-recursive
-- production for ?:, and is defined over the second expression table, 
-- exprTable, which consists of operators that bind tighter than ?:.  The terms
-- of exprTable are atomic expressions, parenthesized expressions, functions and
-- array references.

--{{{ Primary expressions

parseThisRef:: ExpressionParser st
parseThisRef = do
  pos <- getPosition
  reserved "this"
  return (ThisRef pos)

parseNullLit:: ExpressionParser st
parseNullLit = do
  pos <- getPosition
  reserved "null"
  return (NullLit pos)

parseBoolLit:: ExpressionParser st
parseBoolLit = do
    pos <- getPosition
    let parseTrueLit  = reserved "true"  >> return (BoolLit pos True)
        parseFalseLit = reserved "false" >> return (BoolLit pos False)
    parseTrueLit <|> parseFalseLit

parseVarRef:: ExpressionParser st
parseVarRef = liftM2 VarRef getPosition identifier

parseArrayLit:: ExpressionParser st
parseArrayLit = liftM2 ArrayLit getPosition (squares (parseExpression `sepEndBy` comma))

-- function hii(a, b, c, d, e) :: (int, int, [string, string], vart... -> int) {
--     return 5;
-- }
  
parseFuncExpr = do
  reserved "function"
  pos <- getPosition
  args <- parens (identifier `sepBy` comma)
  functype <- parseType <?> "function type annotation"
  body <- parseBlockStmt
  return $ FuncExpr pos args functype body

--{{{ parsing strings

escapeChars =
 [('\'','\''),('\"','\"'),('\\','\\'),('b','\b'),('f','\f'),('n','\n'),
  ('r','\r'),('t','\t'),('v','\v'),('/','/')]

allEscapes:: String
allEscapes = map fst escapeChars

parseEscapeChar = do
  c <- oneOf allEscapes
  let (Just c') = lookup c escapeChars -- will succeed due to line above
  return c' 

parseAsciiHexChar = do
  char 'x'
  d1 <- hexDigit
  d2 <- hexDigit
  return ((chr.fst.head.readHex) (d1:d2:""))

parseUnicodeHexChar = do
  char 'u'
  liftM (chr.fst.head.readHex) 
        (sequence [hexDigit,hexDigit,hexDigit,hexDigit])
        
isWhitespace ch = ch `elem` " \t"

-- The endWith argument is either single-quote or double-quote, depending on how
-- we opened the string.
parseStringLit' endWith =
  (char endWith >> return "") <|>
  (do try (string "\\'")
      cs <- parseStringLit' endWith
      return $ "'" ++ cs) <|>
  (do char '\\'
      c <- parseEscapeChar <|> parseAsciiHexChar <|> parseUnicodeHexChar <|> 
           char '\r' <|> char '\n'
      cs <- parseStringLit' endWith
      if c == '\r' || c == '\n' 
        then return (c:(dropWhile isWhitespace cs)) 
        else return (c:cs)) <|>
   (liftM2 (:) anyChar (parseStringLit' endWith))

parseStringLit:: ExpressionParser st
parseStringLit = do
  pos <- getPosition
  -- parseStringLit' takes as an argument the quote-character that opened the
  -- string.
  str <- lexeme $ (char '\'' >>= parseStringLit') <|> (char '\"' >>= parseStringLit')
  -- CRUCIAL: Parsec.Token parsers expect to find their token on the first
  -- character, and read whitespaces beyond their tokens.  Without 'lexeme'
  -- above, expressions like:
  --   var s = "string"   ;
  -- do not parse.
  return $ StringLit pos str

--}}}

parseRegexpLit:: ExpressionParser st
parseRegexpLit = do
  let parseFlags = do
        flags <- many (oneOf "mgi")
        return $ \f -> f ('g' `elem` flags) ('i' `elem` flags) 
  let parseEscape = char '\\' >> anyChar
  let parseChar = noneOf "/"
  let parseRe = (char '/' >> return "") <|> 
                (do char '\\'
                    ch <- anyChar -- TOOD: too lenient
                    rest <- parseRe
                    return ('\\':ch:rest)) <|> 
                (liftM2 (:) anyChar parseRe)
  pos <- getPosition
  char '/'
  pat <- parseRe --many1 parseChar
  flags <- parseFlags
  spaces -- crucial for Parsec.Token parsers
  return $ flags (RegexpLit pos pat)

parseObjectLit:: ExpressionParser st
parseObjectLit =
  let parseProp = do
        -- Parses a string, identifier or integer as the property name.  I
        -- apologize for the abstruse style, but it really does make the code
        -- much shorter.
        name <- (liftM (uncurry PropString) 
                       (liftM (\(StringLit p s) -> (p,s)) parseStringLit))
                <|> (liftM2 PropId getPosition identifier)
                <|> (liftM2 PropNum getPosition (do x<-decimal; whiteSpace; return x))
        colon
        val <- assignExpr
        return (name, Nothing, val)
    in do pos <- getPosition
          props <- braces (parseProp `sepEndBy` comma) <?> "object literal"
          return $ ObjectLit pos props

--{{{ Parsing numbers.  From pg. 17-18 of ECMA-262.

hexLit = do
  try (string "0x")
  digits <- many1 (oneOf "0123456789abcdefABCDEF")
  [(hex,"")] <- return $ Numeric.readHex digits
  return (True, hex)

-- Creates a decimal value from a whole, fractional and exponent part.
mkDecimal:: Double -> Double -> Int -> Double
mkDecimal w f e =
  if (f >= 1.0)
    then mkDecimal w (f / 10.0) e
    else (w + f) * (10.0 ^^ e)

exponentPart = do
  oneOf "eE"
  (char '+' >> decimal) <|> (char '-' >> negate `fmap` decimal) <|> decimal

--wrap a parser's result in a Just:
jparser p = p >>= (return . Just) 

decLit = 
  (do whole <- decimal
      mfrac <- option Nothing (jparser (char '.' >> decimal))
      mexp <-  option Nothing (jparser exponentPart)
      if (mfrac == Nothing && mexp == Nothing)
        then return (True, fromIntegral whole)
        else return (False, mkDecimal (fromIntegral whole) 
                                      (fromIntegral (maybe 0 id mfrac))
                                      (fromIntegral (maybe 0 id mexp)))) <|>
  (do frac <- char '.' >> decimal
      exp <- option 0 exponentPart
      return (False, mkDecimal 0.0 (fromIntegral frac) (fromIntegral exp)))

parseNumLit:: ExpressionParser st
parseNumLit = do
    pos <- getPosition
    (isint, num) <- lexeme $ hexLit <|> decLit
    notFollowedBy identifierStart <?> "whitespace"
    if isint
      then return $ IntLit pos (round num) 
      else return $ NumLit pos num

--}}}

------------------------------------------------------------------------------
-- Position Helper
------------------------------------------------------------------------------

withPos cstr p = do { pos <- getPosition; e <- p; return $ cstr pos e }

-------------------------------------------------------------------------------
-- Compound Expression Parsers
-------------------------------------------------------------------------------

dotRef e = (reservedOp "." >> withPos cstr identifier) <?> "property.ref"
    where cstr pos key = DotRef pos e key

funcApp e = (parens $ withPos cstr (parseExpression `sepBy` comma)) <?> "(function application)"
    where cstr pos args = CallExpr pos e [] args


tyApp e = do
  p <- getPosition
  reservedOp "@"
  tys <- brackets (type_ `sepBy1` comma)
  return (foldr (\ty e -> TyAppExpr p e ty) e tys)


bracketRef e = (brackets $ withPos cstr parseExpression) <?> "[property-ref]"
    where cstr pos key = BracketRef pos e key

-------------------------------------------------------------------------------
-- Expression Parsers
-------------------------------------------------------------------------------

parseParenExpr:: ExpressionParser st
parseParenExpr = withPos ParenExpr (parens parseListExpr)

-- everything above expect functions
parseExprForNew = parseThisRef <|> parseNullLit <|> parseBoolLit <|> parseStringLit 
  <|> parseArrayLit <|> parseParenExpr <|> parseNewExpr <|> parseNumLit 
  <|> parseRegexpLit <|> parseObjectLit <|> parseVarRef

-- all the expression parsers defined above
parseSimpleExpr' = parseThisRef <|> parseNullLit <|> parseBoolLit 
  <|> parseStringLit <|> parseArrayLit <|> parseParenExpr
  <|> parseFuncExpr <|> parseNumLit <|> parseRegexpLit <|> parseObjectLit
  <|> parseVarRef

parseNewExpr =
  (do pos <- getPosition
      reserved "new"
      constructor <- parseSimpleExprForNew Nothing -- right-associativity
      arguments <- (try (parens (parseExpression `sepBy` comma))) <|> (return [])
      return (NewExpr pos constructor arguments)) <|>
  parseSimpleExpr'

parseSimpleExpr (Just e) = (do
    e' <- dotRef e <|> tyApp e <|> funcApp e <|> bracketRef e
    parseSimpleExpr $ Just e') <|> (return e)
parseSimpleExpr Nothing = do
  e <- parseNewExpr <?> "expression (3)"
  parseSimpleExpr (Just e)

parseSimpleExprForNew (Just e) = (do
    e' <- dotRef e <|> bracketRef e
    parseSimpleExprForNew $ Just e') <|> (return e)
parseSimpleExprForNew Nothing = do
  e <- parseNewExpr <?> "expression (3)"
  parseSimpleExprForNew (Just e)
    
--}}}

makeInfixExpr str constr = Infix parser AssocLeft where
  parser:: CharParser st (Expression SourcePos -> Expression SourcePos -> Expression SourcePos)
  parser = do
    pos <- getPosition
    reservedOp str
    return (InfixExpr pos constr)  -- points-free, returns a function

makePrefixExpr str constr = Prefix parser where
  parser = do
    pos <- getPosition
    (reservedOp str <|> reserved str)
    return (PrefixExpr pos constr) -- points-free, returns a function
    

parsePrefixedExpr = do
  pos <- getPosition
  op <- optionMaybe $ (reservedOp "!" >> return PrefixLNot) <|> 
                      (reservedOp "~" >> return PrefixBNot) <|>
                      (try (lexeme $ char '-' >> notFollowedBy (char '-')) >>
                       return PrefixMinus) <|>
                      (try (lexeme $ char '+' >> notFollowedBy (char '+')) >>
                       return PrefixPlus) <|>
                      (reserved "typeof" >> return PrefixTypeof) <|>
                      (reserved "delete" >> return PrefixDelete)
  case op of
    Nothing -> unaryAssignExpr
    Just op -> do
      innerExpr <- parsePrefixedExpr
      return (PrefixExpr pos op innerExpr)

exprTable:: [[Operator Char st ParsedExpression]]
exprTable =
  [
   [makeInfixExpr "*" OpMul, makeInfixExpr "/" OpDiv, makeInfixExpr "%" OpMod],
   [makeInfixExpr "+" OpAdd, makeInfixExpr "-" OpSub],
   [makeInfixExpr "<<" OpLShift, makeInfixExpr ">>" OpSpRShift,
    makeInfixExpr ">>>" OpZfRShift],
   [makeInfixExpr "<" OpLT, makeInfixExpr "<=" OpLEq, makeInfixExpr ">" OpGT,
    makeInfixExpr ">=" OpGEq, 
    makeInfixExpr "instanceof" OpInstanceof, makeInfixExpr "in" OpIn],
   [makeInfixExpr "==" OpEq, makeInfixExpr "!=" OpNEq,
    makeInfixExpr "===" OpStrictEq, makeInfixExpr "!==" OpStrictNEq],
   [makeInfixExpr "&" OpBAnd], 
   [makeInfixExpr "^" OpBXor], 
   [makeInfixExpr "|" OpBOr],
   [makeInfixExpr "&&" OpLAnd],
   [makeInfixExpr "||" OpLOr]  
  ]
  
parseExpression' = 
  buildExpressionParser exprTable parsePrefixedExpr <?> "simple expression"

--{{{ Parsing ternary operators: left factored

parseTernaryExpr':: CharParser st (ParsedExpression,ParsedExpression)
parseTernaryExpr' = do
    reservedOp "?"
    l <- assignExpr
    colon
    r <- assignExpr
    return $(l,r)

parseTernaryExpr:: ExpressionParser st
parseTernaryExpr = do
  e <- parseExpression'
  e' <- optionMaybe parseTernaryExpr'
  case e' of
    Nothing -> return e
    Just (l,r) -> do p <- getPosition
                     return $ CondExpr p e l r

asLValue :: SourcePos
         -> Expression SourcePos 
         -> CharParser st (LValue SourcePos)
asLValue p' e = case e of
  VarRef p (Id _ x) -> return (LVar p x)
  DotRef p e (Id _ x) -> return (LDot p e x)
  BracketRef p e1 e2 -> return (LBracket p e1 e2)
  otherwise -> fail $ "expeceted l-value at " ++ show p'
 
lvalue :: CharParser st (LValue SourcePos)
lvalue = do
  p <- getPosition
  e <- parseSimpleExpr Nothing
  asLValue p e
 
 
unaryAssignExpr :: CharParser st ParsedExpression
unaryAssignExpr = do
  p <- getPosition
  let prefixInc = do
        reservedOp "++"
        liftM (UnaryAssignExpr p PrefixInc) lvalue
  let prefixDec = do
        reservedOp "--"
        liftM (UnaryAssignExpr p PrefixDec) lvalue
  let postfixInc e = do
        reservedOp "++"
        liftM (UnaryAssignExpr p PostfixInc) (asLValue p e)
  let postfixDec e = do
        reservedOp "--"
        liftM (UnaryAssignExpr p PostfixDec) (asLValue p e)
  let other = do
        e <- parseSimpleExpr Nothing
        postfixInc e <|> postfixDec e <|> return e
  prefixInc <|> prefixDec <|> other


assignOp :: CharParser st AssignOp
assignOp = 
  (reservedOp "=" >> return OpAssign) <|>
  (reservedOp "+=" >> return OpAssignAdd) <|>
  (reservedOp "-=" >> return OpAssignSub) <|>
  (reservedOp "*=" >> return OpAssignMul) <|>
  (reservedOp "/=" >> return OpAssignDiv) <|>
  (reservedOp "%=" >> return OpAssignMod) <|>
  (reservedOp "<<=" >> return OpAssignLShift) <|>
  (reservedOp ">>=" >> return OpAssignSpRShift) <|>
  (reservedOp ">>>=" >> return OpAssignZfRShift) <|>
  (reservedOp "&=" >> return OpAssignBAnd) <|>
  (reservedOp "^=" >> return OpAssignBXor) <|>
  (reservedOp "|=" >> return OpAssignBOr)


pack :: ExpressionParser st
pack = do
  let pack_ :: ExpressionParser st
      pack_ = do
        p <- getPosition
        reserved "pack"
        t_c <- type_
        t <- type_
        reserved "in"
        e <- pack
        return (PackExpr p e t_c t)
  pack_ <|> parseTernaryExpr


assignExpr :: ExpressionParser st
assignExpr = do
  p <- getPosition
  lhs <- pack
  let assign = do
        op <- assignOp
        lhs <- asLValue p lhs
        rhs <- assignExpr
        return (AssignExpr p op lhs rhs)
  assign <|> (return lhs)


expr :: ExpressionParser st
expr = assignExpr  


parseExpression:: ExpressionParser st
parseExpression = assignExpr


externalStmt = do
  pos <- getPosition
  reserved "external"
  id <- identifier
  t <- parseType
  semi
  return (ExternalStmt pos id t)
typeStmt = do
  pos <- getPosition
  isSealed <- option False (reserved "sealed" >> return True)
  reserved "type"
  id <- identifier
  let (Id _ idn) = id
  t' <- parseType
  t <- case (isSealed, t') of
    (False, _) -> return t'
    (True, TObject brand ps) -> 
      return $ (TObject brand
                              (("@sealed_"++idn, True, TObject "__" []):ps))
    (True, TObject brand ps) -> 
      return $ TObject brand (("@sealed_"++idn, True, TObject "__" []):ps)
    (True, t) -> fail "can only seal object types"
  semi
  return (TypeStmt pos id t)

parseToplevel :: ToplevelParser st
parseToplevel = externalStmt <|> typeStmt

parseToplevels = do
  whiteSpace
  parseToplevel `sepBy` whiteSpace

parseListExpr =
  liftM2 ListExpr getPosition (assignExpr `sepBy1` comma)

--}}}

parseScript:: CharParser state ([ToplevelStatement SourcePos], 
                                 JavaScript SourcePos)
parseScript = do
  whiteSpace
  toplevels <- parseToplevels
  script <- liftM2 Script getPosition (parseStatement `sepBy` whiteSpace)
  return (toplevels, script)

parseJavaScriptFromFile :: MonadIO m => String 
                        -> m ([ToplevelStatement SourcePos], 
                              [Statement SourcePos])
parseJavaScriptFromFile filename = do
  chars <- liftIO $ readFile filename
  case parse parseScript filename chars of
    Left err               -> fail (show err)
    Right (toplevs, (Script _ stmts)) -> return (toplevs, stmts)


parseScriptFromString :: String -> String 
                      -> Either ParseError ([ToplevelStatement SourcePos],
                                            JavaScript SourcePos)
parseScriptFromString src script = parse parseScript src script

emptyParsedJavaScript = 
  Script (error "Parser.emptyParsedJavaScript--no annotation") []

--parse a series of toplevels, then parse a script
parseTypedJavaScript :: String -> String -> ([ToplevelStatement SourcePos],
                                             [Statement SourcePos])
parseTypedJavaScript src str = case parse parseScript src str of
    Left err -> error (show err )
    Right (toplevels, (Script _ stmts)) -> (toplevels, stmts)

parseString :: String -> ([ToplevelStatement SourcePos],[Statement SourcePos])
parseString str = case parse parseScript "" str of
  Left err -> error (show err)
  Right (toplevels, (Script _ stmts)) -> (toplevels, stmts)

