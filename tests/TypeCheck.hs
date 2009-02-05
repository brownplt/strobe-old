-- |Type-checker test cases.  The .test files in the type-check directory are
-- parsed as:
--
-- tests ::= test ;
--         | test ; tests
--
-- test ::= expression :: type
--        | expression @@ fails
--
-- expression and type are defined in TypedJavaScript.Parser.
--
-- Note that there is a trailing ';' at the end of a list of tests.
-- JavaScript-style comments are permitted in .test files.
module TypeCheck where

import Text.ParserCombinators.Parsec
import Test.HUnit
import qualified Control.Exception as E

import TypedJavaScript.Syntax (Type,Expression)
import TypedJavaScript.Lexer (semi,reservedOp,reserved)
import TypedJavaScript.Parser (parseType,parseExpression)
import TypedJavaScript.TypeChecker (typeOfExpr,coreTypeEnv,coreVarEnv,
  resolveType)
import TypedJavaScript.Test
import TypedJavaScript.PrettyPrint

assertType :: Expression SourcePos -> Type SourcePos -> Assertion
assertType expr expectedType = do
  actualType <- typeOfExpr coreVarEnv coreTypeEnv expr
  let resolvedType = resolveType coreVarEnv coreTypeEnv expectedType
  -- Assumes equality for types is defined modulo annotation (SourcePos)
  -- TODO: check a subtype, instead of strict equality?
  assertEqual "type mismatch" actualType resolvedType

assertTypeError :: Expression SourcePos -> Assertion
assertTypeError expr = do
  result <- E.try (typeOfExpr coreVarEnv coreTypeEnv expr)
  case result of
    Left (err::(E.SomeException)) -> return () -- error expected
    Right exprType -> assertFailure ("Expected fail, got: " ++ (show $ pp exprType))

parseTestCase :: CharParser st Test
parseTestCase = (do
  expr <- parseExpression
  let typeOK = do
        expectedType <- parseType -- requires a prefixed ::
        return $ TestCase (assertType expr expectedType)
  let typeError = do
        reservedOp "@@" -- random symbol that is not recognized by the
                        -- expression parser.
        reserved "fails"
        return $ TestCase (assertTypeError expr)
  typeOK <|> typeError) <|> (do return $ TestCase $ assertEqual "empty test case" True True)
  
readTestFile :: FilePath -> IO Test
readTestFile path = do
  result <- parseFromFile (parseTestCase `endBy` semi) path
  case result of
    -- Reporting the parse error is deferred until the test is run.
    Left err -> return $ TestCase (assertFailure (show err))
    Right tests -> return $ TestList tests
    
main = do
  testPaths <- getPathsWithExtension ".test" "type-check"
  testCases <- mapM readTestFile testPaths
  return (TestList testCases)
