-- |Environment test cases.  The .test files in the environment directory are
-- parsed as:
--
-- tests ::= test ;
--         | ;
--         | test ; tests
--
-- test ::= ( identifier * ) function-expression
--
-- function-expression is defined in TypedJavaScript.Parser.  Each test
-- lists the the local variables of the associated function.  The test
-- succeeds if all local variables are accounted for.  If the function
-- body repeats a declaration for a variable, the identifier must
-- be duplicated in the identifier list.
--
--
-- Note that there is a trailing ';' at the end of a list of tests.
-- JavaScript-style comments are permitted in .test files.
--
-- The funcEnv function will signal an error only if it is supplied with
-- an expression that is not a FuncExpr.  Since this is trivial, we don't
-- test for errors.
module Environment where

import Text.ParserCombinators.Parsec
import Test.HUnit
import qualified Data.List as L

import TypedJavaScript.Syntax (Expression,Id(..))
import TypedJavaScript.Lexer (semi,identifier,parens)
import TypedJavaScript.Parser (parseFuncExpr)
import TypedJavaScript.Environment (funcEnv)
import TypedJavaScript.Test
import TypedJavaScript.PrettyPrint

assertEnv :: [String] -> Expression SourcePos -> Assertion
assertEnv expectedIds expr = do
  let env = funcEnv expr
  let envIds = map (\((Id _ s),_) -> s) env
  assertEqual "environment mismatch" (L.sort expectedIds) (L.sort envIds) 

parseTestCase :: CharParser st Test
parseTestCase = do
  let testEmpty = return $ TestCase (return ())
  let testEnv = do
        ids <- parens (many identifier)
        expr <- parseFuncExpr 
        return (TestCase $ assertEnv ids expr)
  testEnv <|> testEmpty
  
readTestFile :: FilePath -> IO Test
readTestFile path = do
  result <- parseFromFile (parseTestCase `endBy` semi) path
  case result of
    -- Reporting the parse error is deferred until the test is run.
    Left err -> return $ TestCase (assertFailure (show err))
    Right tests -> return $ TestList tests
    
main = do
  testPaths <- getPathsWithExtension ".test" "environment"
  testCases <- mapM readTestFile testPaths
  return (TestList testCases)
