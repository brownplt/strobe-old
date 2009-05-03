module BrownPLT.IDL.Lexer where

import Prelude hiding (lex)
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as T


identifierStart = (letter <|> oneOf "$_")


lex = T.makeTokenParser $ T.LanguageDef 
  "/*" "*/" "//"
  False -- no nested comments
  letter -- identifier star
  (alphaNum <|> oneOf ":_") -- identifier rest
  (oneOf "{}<>()~.,?:|&^=!+-*/%!@") -- operator start
  (oneOf "=<>|&+@:") -- operator rest
  ["module", "typedef", "interface", "const", "in", "unsigned", "readonly",
   "attribute", "int", "short", "long", "boolean", "raises"]
  ["=", ":"]
  True -- case-sensitive
            

-- everything but commaSep and semiSep
identifier = T.identifier lex
reserved = T.reserved lex
operator = T.operator lex
reservedOp = T.reservedOp lex	
charLiteral = T.charLiteral lex	
stringLiteral = T.stringLiteral lex	
natural = T.natural lex	
integer = T.integer lex	
float = T.float lex	
naturalOrFloat = T.naturalOrFloat lex	
decimal = T.decimal lex	
hexadecimal = T.hexadecimal lex	
octal = T.octal lex	
symbol = T.symbol lex	
whiteSpace = T.whiteSpace lex	
parens = T.parens lex
braces = T.braces lex
angles = T.angles lex
squares = T.squares lex	
semi = T.semi lex
comma = T.comma lex
colon = T.colon lex	
dot = T.dot lex
brackets = T.brackets lex
lexeme = T.lexeme lex
