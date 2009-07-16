-- |Parser for the test suite
--
-- testcase ::= relations { relation [;*] }
--            | expressions { expression [;*] }
--
-- relation ::= [fail] type = type
--            | [fail] type <: type
--
-- expression ::= fail expr
--              | expr :: type
module BrownPLT.TypedJS.TestParser
  ( parseTestFile
  ) where


import Text.ParserCombinators.Parsec
import Test.HUnit
import TypedJavaScript.Syntax (Expression)
import TypedJavaScript.Lexer (semi, reservedOp, reserved, whiteSpace, braces)
import qualified TypedJavaScript.Parser as Parser
import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.TypeTheory
import BrownPLT.TypedJS.TypeCheck
import TypedJavaScript.PrettyPrint


xor :: Bool -> Bool -> Bool
xor True False = True
xor False True = True
xor _ _ = False


testcase :: CharParser st Test
testcase = relations <|> expressions
  where relations = do
          reserved "relations"
          liftM TestList (braces $ relation `sepBy` semi)
        expressions = do
          reserved "expressions"
          liftM TestList (braces $ expression `sepBy` semi)


relation :: CharParser st Test
relation = do
  p <- getPosition
  isFail <- option False (reserved "fail" >> return True)
  t1 <- Parser.parseType'
  let eq = do
        reservedOp "="
        t2 <- Parser.parseType'
        return $ TestCase $ do
          assertBool (show p) $
            (canonize t1 == canonize t2) `xor` isFail
  let sub = do
        reservedOp "<:"
        t2 <- Parser.parseType'
        return $ TestCase $ do
          assertBool (show p) $
            (isSubtype (canonize t1) (canonize t2)) `xor` isFail
  eq <|> sub


expression :: CharParser st Test
expression = do
  p <- getPosition
  isFail <- option False (reserved "fail" >> return True)
  e <- Parser.parseExpression
  case isFail of
    False -> do
      reservedOp "::"
      t <- Parser.parseType'
      return $ TestCase $ case typeCheckExpr e of
        -- typeCheckExpr should return the type in canonical form
        Right s -> assertBool (show p) (isSubtype s (canonize t))
        Left err -> assertFailure (show p ++ ": " ++ err)
    True -> return $ TestCase $ case typeCheckExpr e of
      Left err -> return ()
      Right s -> assertFailure $ printf 
        "%s: expected ill-typed expression; has type %s" (show p) (renderType s)


testFile :: CharParser st Test
testFile = do
  whiteSpace
  ts <- many testcase
  eof
  return (TestList ts)


parseTestFile :: SourceName -> IO Test
parseTestFile path = do
  r <- parseFromFile testFile path
  case r of
    Left err -> fail (show err)
    Right t -> return t
