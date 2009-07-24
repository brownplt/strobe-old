-- |Parser for the test suite
--
-- testcase ::= relations { relation [;*] }
--            | expressions { expression [;*] }
--
-- relation ::= [fail] type = type
--            | [fail] type <: type
--
-- expression ::= fail expr
--              | succeed expr
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
import BrownPLT.TypedJS.InitialEnvironment
import Control.Exception as E


xor :: Bool -> Bool -> Bool
xor True False = True
xor False True = True
xor _ _ = False


catchException :: SourcePos
               -> Assertion
               -> Assertion
catchException p assert =E.catch assert f
  where f exp = case exp of
          E.ErrorCall e ->  
            fail $ printf "uncaught exception at %s: %s" (show p) e


testcase :: InitialStoreEnv -> CharParser st Test
testcase idl = relations <|> expressions
  where relations = do
          reserved "relations"
          liftM TestList (braces $ relation idl `sepBy` semi)
        expressions = do
          reserved "expressions"
          liftM TestList (braces $ expression idl `sepBy` semi)


relation :: InitialStoreEnv -> CharParser st Test
relation init = do
  p <- getPosition
  isFail <- option False (reserved "fail" >> return True)
  t1 <- Parser.parseType'
  let eq = do
        reservedOp "="
        t2 <- Parser.parseType'
        let s = printf "%s : %s %s = %s" (show p) 
                  (if isFail then "fail" else "")
                  (renderType t1) (renderType t2)
        return $ TestCase $ catchException p $ do
          assertBool s $ runTypeCheckWithoutError init $ do
            u1 <- canonize t1
            u2 <- canonize t2
            return ((u1 == u2) `xor` isFail)
  let sub = do
        reservedOp "<:"
        t2 <- Parser.parseType'
        let s = printf "%s : %s %s <: %s" (show p) 
                  (if isFail then "fail" else "")
                  (renderType t1) (renderType t2)
        return $ TestCase $ catchException p $ do
          assertBool s $ runTypeCheckWithoutError init $ do
            u1 <- canonize t1
            u2 <- canonize t2
            r <- isSubtype u1 u2
            return (r `xor` isFail)
  eq <|> sub


expression' :: InitialStoreEnv -> CharParser st Test
expression' idl = do
  p <- getPosition
  isFail <- option False (reserved "fail" >> return True)
  e <- Parser.parseExpression
  case isFail of
    False -> do
      reservedOp "::"
      t <- Parser.parseType'
      return $ TestCase $ catchException p $ case typeCheckExpr idl e of
        -- typeCheckExpr should return the type in canonical form
        Right s -> do
          assertBool (show p) $ runTypeCheckWithoutError idl $ do
            t <- canonize t
            t <- brandSugar t
            isSubtype s t
        Left err -> assertFailure (show p ++ ": expected succeess got, " ++ err)
    True -> return $ TestCase $ catchException p $ case typeCheckExpr idl e of
      Left err -> return ()
      Right s -> assertFailure $ printf 
        "%s: expected ill-typed expression; has type %s" (show p) (renderType s)


expressionSucceed :: InitialStoreEnv -> CharParser st Test
expressionSucceed idl = do
  p <- getPosition
  reserved "succeed"
  e <- Parser.parseExpression
  return $ TestCase $ catchException p $ case typeCheckExpr idl e of
    Right _ -> return ()
    Left err -> assertFailure (show p ++ ": " ++ err)


expression idl = expressionSucceed idl <|> expression' idl


testFile :: InitialStoreEnv -> CharParser st Test
testFile idl = do
  whiteSpace
  ts <- many (testcase idl)
  eof
  return (TestList ts)


parseTestFile :: InitialStoreEnv -> SourceName -> IO Test
parseTestFile idl path = do
  r <- parseFromFile (testFile idl) path
  case r of
    Left err -> fail (show err)
    Right t -> return t
