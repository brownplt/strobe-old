module TypedJavaScript.Parser
  ( parseScript
  , parseExpression
  , parseType
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
  , parseAssignExpr
  , parseToplevel, parseToplevels
  , parseTypedJavaScript
  ) where

import qualified TypedJavaScript.Types as Types
import qualified BrownPLT.JavaScript.Analysis.ANF as ANF
import TypedJavaScript.Lexer hiding (identifier)
import qualified TypedJavaScript.Lexer as Lexer
import TypedJavaScript.Syntax
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Control.Monad(liftM,liftM2)
import Control.Monad.Trans (MonadIO,liftIO)
import Numeric(readDec,readOct,readHex)
import Data.Char(chr)
import Data.Char
import qualified Data.List as L
 
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

{- typeConstraint ::= identifier <: type
                    | ( type ) <: type

   The obvious production, type <: type, conflicts with const<type [,*]> and is
   not LL-parsable.
 -}
typeConstraint :: CharParser st TypeConstraint
typeConstraint = do
  t1 <- (Lexer.identifier >>= \x -> return (TId x)) <|> (parens type_)
  reservedOp "<:"
  t2 <- type_
  return (TCSubtype t1 t2)

{- The syntax for types is:

 type ::= identifier
        | 'literal
        | type?
        | '[' type ']' type [,*] -> type?     ; explicit this
        | '[' type ']' type [,+] ... -> type? ; explicit this
        | type [,*] -> type?
        | type [,+] ... -> type?
        | constr<type [,*]>
        | forall identifier+ . type
        | forall identifier+ : typeConstraint+ . type
        | rec identifier . type
        | ( type )

Disambiguation:

 type ::= forall identifier+ . type_fn
        | forall identifier+ : typeConstraint+ . type
        | rec identifier . type
        | '[' type ']' type' [,*] -> type?
        | '[' type ']' type' [,+] ... -> type?
        | type_fn

 type_fn ::= type' [,*] -> type?
           | type' [,+] ... -> type?
           | type'

 type' ::= type''?
         | type''

 type'' ::= identifier
          | ( type )
          | { id: type' [,* }
          | constr<type [,*]>
          | 'literal

 -} 

type_ :: CharParser st (Type)
type_ = do
  let forall = do
        p <- getPosition
        reserved "forall"
        ids <- many1 Lexer.identifier
        constraints <- (reservedOp ":" >> many1 typeConstraint) <|> 
                       (return [])
        reservedOp "."
        t <- type_fn
        return (TForall ids constraints t)
  let rec = do
        p <- getPosition
        reserved "rec"
        id <- Lexer.identifier
        reservedOp "."
        t <- type_
        return (TRec id t)
  let explicitThis = do
        thisType <- brackets type_
        ts <- type_' `sepBy` comma
        let vararity = do
              reservedOp "..."
              reservedOp "->"
              r <- type_ <|> (return Types.undefType)
              return (TFunc (thisType:(L.init ts)) (Just $L.last ts) r (LPNone))
        let func = do
              reservedOp "->"
              r <- type_ <|> (return Types.undefType)
              return (TFunc (thisType:ts) Nothing r (LPNone))
        case ts of
          []  -> func -- function of zero arguments
          [t] -> vararity <|> func <|> (return t)
          ts  -> vararity <|> func
  forall <|> rec <|> explicitThis <|> type_fn

type_fn :: CharParser st (Type)
type_fn = do
  p <- getPosition
  let globalThis = TObject [] -- TODO: make this the global this
  ts <- type_' `sepBy` comma
  let vararity = do
        reservedOp "..."
        reservedOp "->"
        r <- type_ <|> (return Types.undefType)
        return (TFunc (globalThis:(L.init ts)) (Just $L.last ts) r LPNone)
  let func = do
        reservedOp "->"
        r <- type_ <|> (return Types.undefType)
        return (TFunc (globalThis:ts) Nothing r LPNone)
        --Nonte: latent predicates really aren't part of the syntax,
        --but the parser has to deal with them. type checker should fill
        --them in properly.
  case ts of
    []  -> func -- function of zero arguments
    [t] -> vararity <|> func <|> (return t)
    ts  -> vararity <|> func

type_' :: CharParser st (Type)
type_' = do
  t <- type_''
  let nullable = do
        reservedOp "?"
        return (TUnion [t, Types.undefType])
  let extended = do
        parens $ reservedOp "<-"
        rt <- type_
        return (TExtend t rt)
  nullable <|> extended <|> (return t) <?> "possibly nullable type"

type_'' :: CharParser st (Type)
type_'' =
  let union = do 
        reservedOp "U";
        liftM TUnion (parens (type_'' `sepEndBy` comma))
      object = do
        fields <- braces $ field `sepEndBy` comma
        fields' <- noDupFields fields
        return (TObject fields')
      noDupFields fields
        | length (L.nub $ map fst fields) == length fields = return fields
        | otherwise = fail "duplicate fields in an object type specification"
    in (parens type_) <|> (try union) <|> object <|> constrOrId


toANFLit :: Expression SourcePos -> ANF.Lit SourcePos
toANFLit (StringLit p s) = ANF.StringLit p s
toANFLit (NumLit p x) = ANF.NumLit p x
toANFLit (IntLit p n) = ANF.IntLit p n
toANFLit (BoolLit p b) = ANF.BoolLit p b
toANFLit e = error $ "toANFLit: cannot use " ++ show e ++ " as a literal type"

constrOrId :: CharParser st (Type)
constrOrId = do
  id <- (identifier >>= \(Id _ id) -> return id)
  let constr = do
        args <- (angles $ type_' `sepBy` comma) <?> "type application"
        return (TApp (TId id) args)
  constr <|> (return (TId id))

field :: CharParser st (String, Type)
field = do
  id <- Lexer.identifier
  reservedOp "::"
  t <- type_' 
  return (id,t)
  
parseType :: TypeParser st
parseType = do
  reservedOp "::" <?> "type annotation (:: followed by a type)"
  t <- type_
  return t

parseMaybeType :: MaybeTypeParser st
parseMaybeType = do
  (do t <- parseType
      return (Just t)) <|> (return Nothing)

--{{{ Statements

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
        (reserved "var" >> liftM VarInit (parseVarDecl `sepBy` comma)) <|>
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

-- a vardecl is one of: 
--         a = X
--         a :: type = X
--         a :: type
parseVarDecl ::  CharParser st (VarDecl SourcePos)
parseVarDecl = do
  pos <- getPosition
  id <- identifier
  (do reservedOp "="  --expression with no type annotation
      expr <- parseExpression
      return (VarDeclExpr pos id Nothing expr)) <|>
    (do thetype <- parseType <?> "expression or type annotation" 
        (do reserved "="
            expr <- parseExpression                               --expression with type
            return (VarDeclExpr pos id (Just thetype) expr)) <|> 
              (do return (VarDecl pos id thetype)))               --just type, no expression
    
parseVarDeclStmt:: StatementParser st
parseVarDeclStmt = do 
  pos <- getPosition
  reserved "var"
  decls <- parseVarDecl `sepBy` comma
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
  return (VarDeclStmt pos [VarDeclExpr pos name (Just functype) (FuncExpr pos args functype body)])

parseConstructorStmt :: StatementParser st
parseConstructorStmt = do
  fail "Consructors not yet implemented" {-
  pos <- getPosition
  name <- try (reserved "constructor" >> identifier) -- TODO: remove this 'try'?
  args <- parens ((do id <- identifier 
                      thetype <- parseType
                      return (id, thetype)) `sepBy` comma)
  body <- parseBlockStmt <?> "function body in { ... }"
  return (ConstructorStmt pos name args [] Nothing body) -}

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
  <|> parseVarDeclStmt  <|> parseFunctionStmt
  -- added for tJS
  <|> parseConstructorStmt 
  
  -- labelled, expression and the error message always go last, in this order
  <|> parseLabelledStmt <|> parseExpressionStmt <?> "statement"

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
        typeannot <- parseMaybeType
        colon
        val <- parseAssignExpr
        return (name,typeannot,val)
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

parameterizedFuncApp e = do
  reservedOp "@" 
  p <- getPosition
  types <- brackets $ (parens type_) `sepBy` comma
  args <- parens $ parseExpression `sepBy` comma
  return (CallExpr p e types args)

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
    e' <- dotRef e <|> funcApp e <|> parameterizedFuncApp e <|> bracketRef e
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
    
mkPrefix operator constr = Prefix $ do
  pos <- getPosition
  operator
  return (\operand -> PrefixExpr pos constr operand)

makePostfixExpr str constr = Postfix parser where
  parser = do
    pos <- getPosition
    (reservedOp str <|> reserved str)
    return (PostfixExpr pos constr) -- points-free, returns a function

prefixIncDecExpr = do
  pos <- getPosition
  op <- optionMaybe $ (reservedOp "++" >> return PrefixInc) <|>
                      (reservedOp "--" >> return PrefixDec)
  case op of
    Nothing -> parseSimpleExpr Nothing
    Just op -> do
      innerExpr <- parseSimpleExpr Nothing -- TODO: must be an l-val, I think
      return (PrefixExpr pos op innerExpr)

-- apparently, expression tables can't handle immediately-nested prefixes

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
    Nothing -> prefixIncDecExpr  -- new is treated as a simple expr
    Just op -> do
      innerExpr <- parsePrefixedExpr
      return (PrefixExpr pos op innerExpr)

exprTable:: [[Operator Char st ParsedExpression]]
exprTable =
  [
   [makePrefixExpr "++" PrefixInc,
    makePostfixExpr "++" PostfixInc],
   [makePrefixExpr "--" PrefixDec,
    makePostfixExpr "--" PostfixDec],
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
    l <- parseAssignExpr
    colon
    r <- parseAssignExpr
    return $(l,r)

parseTernaryExpr:: ExpressionParser st
parseTernaryExpr = do
  e <- parseExpression'
  e' <- optionMaybe parseTernaryExpr'
  case e' of
    Nothing -> return e
    Just (l,r) -> do p <- getPosition
                     return $ CondExpr p e l r
--}}}

-- Parsing assignment operations.
makeAssignExpr str constr = Infix parser AssocRight where
  parser:: CharParser st (ParsedExpression -> ParsedExpression -> ParsedExpression)
  parser = do
    pos <- getPosition
    reservedOp str
    return (AssignExpr pos constr)

assignTable:: [[Operator Char st ParsedExpression]]
assignTable = [
  [makeAssignExpr "=" OpAssign, makeAssignExpr "+=" OpAssignAdd, 
    makeAssignExpr "-=" OpAssignSub, makeAssignExpr "*=" OpAssignMul,
    makeAssignExpr "/=" OpAssignDiv, makeAssignExpr "%=" OpAssignMod,
    makeAssignExpr "<<=" OpAssignLShift, makeAssignExpr ">>=" OpAssignSpRShift,
    makeAssignExpr ">>>=" OpAssignZfRShift, makeAssignExpr "&=" OpAssignBAnd,
    makeAssignExpr "^=" OpAssignBXor, makeAssignExpr "|=" OpAssignBOr
  ]]


parseAssignExpr:: ExpressionParser st
parseAssignExpr = buildExpressionParser assignTable parseTernaryExpr  

parseExpression:: ExpressionParser st
parseExpression = parseAssignExpr


externalStmt = do
  pos <- getPosition
  reserved "external"
  id <- identifier
  t <- parseType
  semi
  return (ExternalStmt pos id t)
typeStmt = do
  pos <- getPosition
  reserved "type"
  id <- identifier
  t <- parseType
  semi
  return (TypeStmt pos id t)

parseToplevel :: ToplevelParser st
parseToplevel = externalStmt <|> typeStmt

parseToplevels = do
  whiteSpace
  res <- parseToplevel `sepBy` whiteSpace
  return res

parseListExpr =
  liftM2 ListExpr getPosition (parseAssignExpr `sepBy1` comma)

--}}}

parseScript:: CharParser state (JavaScript SourcePos)
parseScript = do
  whiteSpace
  liftM2 Script getPosition (parseStatement `sepBy` whiteSpace)
  
parseJavaScriptFromFile :: MonadIO m => String -> m [Statement SourcePos]
parseJavaScriptFromFile filename = do
  chars <- liftIO $ readFile filename
  case parse parseScript filename chars of
    Left err               -> fail (show err)
    Right (Script _ stmts) -> return stmts


parseScriptFromString:: String -> String -> Either ParseError (JavaScript SourcePos)
parseScriptFromString src script = parse parseScript src script

emptyParsedJavaScript = 
  Script (error "Parser.emptyParsedJavaScript--no annotation") []

parseTypedJavaScript :: String -> String -> [Statement SourcePos]
parseTypedJavaScript src str = case parse parseScript src str of
  Left err -> error (show err)
  Right (Script _ stmts) -> stmts

parseString :: String -> [Statement SourcePos]
parseString str = case parse parseScript "" str of
  Left err -> error (show err)
  Right (Script _ stmts) -> stmts

