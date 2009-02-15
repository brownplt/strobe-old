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
  ) where

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
 
-- We parameterize the parse tree over source-locations.
type ParsedStatement = Statement SourcePos
type ParsedExpression = Expression SourcePos
type ParsedType = Type SourcePos
type MaybeParsedType = Maybe (Type SourcePos)

-- These parsers can store some arbitrary state
type StatementParser state = CharParser state ParsedStatement
type ExpressionParser state = CharParser state ParsedExpression
type TypeParser state = CharParser state ParsedType
type MaybeTypeParser state = CharParser state MaybeParsedType

identifier =
  liftM2 Id getPosition Lexer.identifier

{- 
  To make this easy:
  
  type = [simpletype : ] funcarg ,* -> [type]
       | simpletype
  
  funcarg = simpletype argsfx
  argsfx = 
         | ?
         | ...

  simpletype = identifier [< type, + >]   --plain id, or generic
             | { identifier :: simpletype ,* }  --object. 'simpletype' instead of 'type' because ',' would be interpreted as a function
             | < expression >             --typeof
             | ( type )                   --parenthesised
   
  =================
  Then some additional computation is done to ensure that args are in the order: required, optional, and at most 1 var.
  This method should be simpler than building it into the parser directly.
-}

--helpers for parseTypeNoColons:
data ArgType = ReqArg | OptArg | VarArg

parseTypeSimple :: TypeParser st 
parseTypeSimple = do
  pos <- getPosition
  (do (Id idpos idstr) <- identifier
      (do innertypes <- angles (parseTypeNoColons `sepBy` comma)
          if length innertypes == 0 
            then fail "generic application must have at least one type" 
            else return (TApp pos (TId idpos idstr) innertypes))
        <|> (return (TId idpos idstr)))
    <|> ((do fields <- braces $ (liftM2 (,) identifier (do reservedOp "::"; parseTypeSimple)) `sepEndBy` comma -- structural object type
             return (TObject pos fields)) <?> "object type")
    -- <|> ((do expr <- angles parseExpression; return (TExpr pos expr)) <?> "<> operator") -- <> operator
    <|> ((parens parseTypeNoColons) <?> "parentheses") -- parens
parseReturnType :: TypeParser st
parseReturnType = do
  reservedOp "->" 
  pos <- getPosition
  parseTypeNoColons <|> (return $ TId pos "undefined")

processArgs :: [(Type a, ArgType)] -> ([Type a], [Type a], Maybe (Type a))
processArgs [] = ([], [], Nothing)
processArgs [(t, mod)] = 
  case mod of 
    ReqArg -> ([t], [], Nothing)
    OptArg -> ([], [t], Nothing)
    VarArg -> ([], [], Just t)
processArgs ((t, mod):(t2, mod2):rest) = 
  case mod of
    ReqArg -> let (r,o,v) = processArgs $ (t2,mod2):rest in (t:r, o, v)
    OptArg -> case mod2 of
                ReqArg -> error "Can't have required argument after optional argument"
                _      -> let (r,o,v) = processArgs $ (t2,mod2):rest in (r, t:o, v)
    VarArg -> error "vararg can't be followed by anything"

-- main parsing functions:
parseTypeNoColons :: TypeParser st
parseTypeNoColons = do
  pos <- getPosition
  thistype <- try (do tt <- parseTypeSimple    --'try' to make sure we don't eat the first required arg
                      reservedOp "|" --changed from ":" to work better with typed object literals
                      return (Just tt)) <|> (return Nothing)
  args <- (do st <- parseTypeSimple
              (reservedOp "?" >> return (st,OptArg))
                <|> (reservedOp "..." >> return (st,VarArg))
                <|> (return (st,ReqArg))) `sepBy` comma
  case args of
    [] -> do
      rettype <- parseReturnType
      return $ TFunc pos thistype [] [] Nothing rettype
    [(argt, mod)] -> (do rettype <- parseReturnType
                         let (r,o,v) = processArgs [(argt, mod)]
                           in return $ TFunc pos thistype r o v rettype)
                       <|> (case mod of
                              ReqArg -> return argt -- non-function
                              OptArg -> fail "unexpected ?"  --TODO: fix these fails, they're very confusing.
                              VarArg -> fail "unexpected ...")
    args' -> (do rettype <- parseReturnType
                 let (r,o,v) = processArgs args'
                   in return $ TFunc pos thistype r o v rettype)

parseType :: TypeParser st
parseType = do
  reservedOp "::" <?> "type annotation (:: followed by a type)"
  t <- parseTypeNoColons
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
                      t <- parseType
                      return (ForInVar id t)) <|>
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
  pos <- getPosition
  name <- try (reserved "function" >> identifier) -- ambiguity with FuncExpr
  args <- parens (identifier `sepBy` comma)
  functype <- parseType <?> "function type annotation"
  body <- parseBlockStmt
  --transform a function statement into an assignment and a funcexpr
  return (VarDeclStmt pos [VarDeclExpr pos name (Just functype) (FuncExpr pos args functype body)])

parseConstructorStmt :: StatementParser st
parseConstructorStmt = do
  pos <- getPosition
  name <- try (reserved "constructor" >> identifier) -- TODO: remove this 'try'?
  args <- parens ((do id <- identifier 
                      thetype <- parseType
                      return (id, thetype)) `sepBy` comma)
  body <- parseBlockStmt <?> "function body in { ... }"
  return (ConstructorStmt pos name args [] Nothing body)

parseTypeStmt :: StatementParser st
parseTypeStmt = do
  pos <- getPosition
  reserved "type"
  id <- identifier
  thetype <- parseType
  semi
  return (TypeStmt pos id thetype)
               
parseStatement:: StatementParser st
parseStatement = parseIfStmt <|> parseSwitchStmt <|> parseWhileStmt 
  <|> parseDoWhileStmt <|> parseContinueStmt <|> parseBreakStmt 
  <|> parseBlockStmt <|> parseEmptyStmt <|> parseForInStmt <|> parseForStmt
  <|> parseTryStmt <|> parseThrowStmt <|> parseReturnStmt
  <|> parseVarDeclStmt  <|> parseFunctionStmt
  -- added for tJS
  <|> parseTypeStmt <|> parseConstructorStmt 
  
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
  pos <- getPosition
  reserved "function"
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

jparser p = do
  rez <- p
  return (Just rez)

decLit = 
  (do whole <- decimal
      mfrac <- option Nothing (jparser (char '.' >> decimal))
      mexp <-  option Nothing (jparser exponentPart)
      if (mfrac == Nothing && mexp == Nothing)
        then return (True, fromIntegral whole)
        else let (Just frac) = mfrac
                 (Just exp)  = mexp
              in return (False, mkDecimal (fromIntegral whole) 
                                          (fromIntegral frac) 
                                          (fromIntegral exp))) <|>
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
    where cstr pos args = CallExpr pos e args

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
    e' <- dotRef e <|> funcApp e <|> bracketRef e
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
   [makeInfixExpr "&" OpBAnd], 
   [makeInfixExpr "^" OpBXor], 
   [makeInfixExpr "|" OpBOr],
   [makeInfixExpr "&&" OpLAnd],
   [makeInfixExpr "||" OpLOr],  
   [makeInfixExpr "==" OpEq, makeInfixExpr "!=" OpNEq,
    makeInfixExpr "===" OpStrictEq, makeInfixExpr "!==" OpStrictNEq]
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

parseString :: String -> [Statement SourcePos]
parseString str = case parse parseScript "" str of
  Left err -> error (show err)
  Right (Script _ stmts) -> stmts
