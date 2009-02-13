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
  resolveType,isSubType)
import TypedJavaScript.Test
import TypedJavaScript.PrettyPrint

showSp :: SourcePos -> String
showSp pos = (sourceName pos) ++ ":" ++ (show $ sourceLine pos)

assertType :: SourcePos -> Expression SourcePos -> Type SourcePos -> Assertion
assertType pos expr expectedType = do
  --actualType <- typeOfExpr coreVarEnv coreTypeEnv expr
  actualType <- E.try (typeOfExpr coreVarEnv coreTypeEnv expr)
  case actualType of
    Left (err::(E.SomeException)) -> assertFailure ((showSp pos) ++ ": user error: " ++ (show err))
    Right exprType -> do
      let resolvedType = resolveType coreVarEnv coreTypeEnv expectedType
      assertBool ((showSp pos) ++ ": type mismatch, " ++ (show exprType) ++ " is not a subtype of " ++ (show resolvedType)) 
                 (isSubType coreVarEnv coreTypeEnv exprType resolvedType)

assertTypeError :: SourcePos -> Expression SourcePos -> Assertion
assertTypeError pos expr = do
  result <- E.try (typeOfExpr coreVarEnv coreTypeEnv expr)
  case result of
    Left (err::(E.SomeException)) -> return () -- error expected
    Right exprType -> assertFailure ((showSp pos) ++ ": expected fail, got: " ++ (show $ pp exprType))

assertTypeSuccess :: SourcePos -> Expression SourcePos -> Assertion
assertTypeSuccess pos expr = do
  result <- E.try (typeOfExpr coreVarEnv coreTypeEnv expr)
  case result of
    Left (err::(E.SomeException)) -> assertFailure ((showSp pos) ++ ": expected success, got: " ++ (show $ err)) 
    Right exprType -> return () -- success expected

parseTestCase :: CharParser st Test
parseTestCase = (do
  pos <- getPosition
  expr <- parseExpression
  let typeOK = do
        expectedType <- parseType -- requires a prefixed ::
        return $ TestCase (assertType pos expr expectedType)
  let typeError = do
        reservedOp "@@" -- random symbol that is not recognized by the
                        -- expression parser.
        reserved "fails"
        return $ TestCase (assertTypeError pos expr)
  let typeSuccess = do
        pos <- getPosition
        reservedOp "@@" -- random symbol that is not recognized by the
                        -- expression parser.
        reserved "succeeds"
        return $ TestCase (assertTypeSuccess pos expr)
   
  typeOK <|> (try typeError) <|> typeSuccess) <|> (do return $ TestCase $ assertEqual "empty test case" True True)
  
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
