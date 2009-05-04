-- |Type-checker test cases.  The .js files in the type-check directory are
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
import qualified Data.Map as M
import TypedJavaScript.Syntax
import TypedJavaScript.Lexer (semi, reservedOp, reserved, whiteSpace)
import TypedJavaScript.Parser (parseType,parseExpression)
import TypedJavaScript.TypeCheck (typeCheck, typeCheckWithGlobals, loadCoreEnv)
import TypedJavaScript.Types (isSubType)
import TypedJavaScript.Test
import TypedJavaScript.PrettyPrint
import BrownPLT.TypedJS.InitialEnvironment

import Text.ParserCombinators.Parsec.Pos (initialPos, SourcePos)

t1 <: t2 = isSubType [] t1 t2

--too lazy to fix the type annotations for these after adding venv, tenv.
--typeOfExpr :: Expression SourcePos -> IO (Type SourcePos)
typeOfExpr expr' venv tenv = do 
  let p = initialPos "testcase"
  let stmt = VarDeclStmt p [VarDeclExpr p (Id p "result")
                                         Nothing
                                         expr']
  env <- typeCheckWithGlobals venv tenv [stmt]
  case M.lookup "result" env of
    Nothing -> fail $ "catastrophic failure: result unbound in " ++ show env
    Just Nothing -> fail "catastrophic result not found"
    
    Just (Just (t, mvp)) -> return t

--assertType :: SourcePos -> Expression SourcePos -> Type SourcePos -> Assertion
assertType pos expr expectedType venv tenv = do
  actualType <- E.try (typeOfExpr expr venv tenv)
  case actualType of
    Left (err::(E.SomeException)) -> assertFailure (
      (showSp pos) ++ ": " ++ (show err))
    Right (exprType) -> do
      assertBool ((showSp pos) ++ ": type mismatch, " ++ 
                  (show exprType) ++ " is not a subtype of " ++ 
                  (show expectedType)) 
                 (exprType <: expectedType)

--assertTypeError :: SourcePos -> Expression SourcePos -> Assertion
assertTypeError pos expr venv tenv = do
  result <- E.try (typeOfExpr expr venv tenv)
  case result of
    Left (err::(E.SomeException)) -> return () -- error expected
    Right (exprType) -> assertFailure (
      (showSp pos) ++ ": expected fail, got: " ++ (show exprType))

--assertTypeSuccess :: SourcePos -> Expression SourcePos -> Assertion
assertTypeSuccess pos expr venv tenv = do
  result <- E.try (typeOfExpr expr venv tenv)
  case result of
    Left (err::(E.SomeException)) -> assertFailure ((showSp pos) ++ ": expected success, got: " ++ (show $ err)) 
    Right exprType -> return () -- success expected

--parseTestCase :: CharParser st Test
parseTestCase venv tenv = (do
  --whiteSpace --TODO: make uncomment work to fix bug
  pos <- getPosition
  expr <- parseExpression
  let typeOK = do
        expectedType <- parseType -- requires a prefixed ::
        return $ TestCase (assertType pos expr expectedType venv tenv)
  let typeError = do
        reservedOp "@@" -- random symbol that is not recognized by the
                        -- expression parser.
        reserved "fails"
        return $ TestCase (assertTypeError pos expr venv tenv)
  let typeSuccess = do
        pos <- getPosition
        reservedOp "@@" -- random symbol that is not recognized by the
                        -- expression parser.
        reserved "succeeds"
        return $ TestCase (assertTypeSuccess pos expr venv tenv)
   
  typeOK <|> (try typeError) <|> typeSuccess) -- <|> 
--    (do return $ TestCase $ assertEqual "empty test case" True True)

parseAllTests venv tenv = do
  whiteSpace
  tests <- parseTestCase venv tenv `endBy` semi
  eof -- ensure the whole file parses
  return tests
  
--readTestFile :: FilePath -> IO Test
readTestFile venv tenv path = do
  result <- parseFromFile (parseAllTests venv tenv) path
  case result of
    -- Reporting the parse error is deferred until the test is run.
    Left err -> return $ TestCase (assertFailure (show err))
    Right tests -> return $ TestList tests
    
main = do
  testPaths <- getPathsWithExtension ".js" "type-check"
  domTypeEnv <- makeInitialEnv
  (venv, tenv) <- loadCoreEnv domTypeEnv
  testCases <- mapM (readTestFile venv (M.union domTypeEnv tenv)) testPaths
  return (TestList testCases)
