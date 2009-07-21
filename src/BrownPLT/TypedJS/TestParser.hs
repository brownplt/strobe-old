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
import BrownPLT.TypedJS.Syntax (Expression)
import BrownPLT.TypedJS.Lexer (semi, reservedOp, reserved, whiteSpace, braces)
import qualified BrownPLT.TypedJS.Parser as Parser
import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.TypeTheory
import BrownPLT.TypedJS.Infrastructure
import BrownPLT.TypedJS.TypeCheck
import BrownPLT.TypedJS.PrettyPrint
import Control.Exception as E


xor :: Bool -> Bool -> Bool
xor True False = True
xor False True = True
xor _ _ = False


catchException :: SourcePos
               -> Assertion
               -> Assertion
catchException p assert = E.catch assert $ 
  \(E.ErrorCall e) -> fail $ printf "%s: %s" (show p) e


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
        return $ TestCase $ catchException p $ do
          assertBool (show p) $ runEnv $ do
            u1 <- canonize t1
            u2 <- canonize t2
            r <- isSubtype u1 u2
            return (r `xor` isFail)
  let sub = do
        reservedOp "<:"
        t2 <- Parser.parseType'
        return $ TestCase $ catchException p $ do
          assertBool (show p) $ runEnv $ do
            u1 <- canonize t1
            u2 <- canonize t2
            r <- isSubtype u1 u2
            return (r `xor` isFail)
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
      return $ TestCase $ catchException p $ case typeCheckExpr e of
        -- typeCheckExpr should return the type in canonical form
        Right s -> assertBool (show p) $ runEnv (canonize t >>= isSubtype s)
        Left err -> assertFailure (show p ++ ": " ++ err)
    True -> return $ TestCase $ catchException p $ case typeCheckExpr e of
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
