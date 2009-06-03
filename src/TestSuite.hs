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
module Main where

import Paths_TypedJavaScript (getDataDir)

import System.Environment
import System.FilePath
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
import BrownPLT.TypedJS.TypeFunctions
import BrownPLT.Testing

import Text.ParserCombinators.Parsec.Pos (initialPos, SourcePos)


typeOfExpr expr' venv tenv = do 
  let p = initialPos "testcase"
  let stmt = VarDeclStmt p [VarDeclExpr p (Id p "result")
                                         Nothing
                                         expr']
  env <- typeCheckWithGlobals venv tenv [stmt]
  case M.lookup "result" env of
    Nothing -> fail $ "catastrophic failure: result unbound in " ++ show env
    Just Nothing -> fail "catastrophic result not found"
    
    Just (Just (tDec, tAct, isLocal)) -> return tAct


assertType pos expr expectedType' venv tenv isSubTypeOf = do
  let expectedType = replaceAliases M.empty tenv pos expectedType'
  actualType <- E.try (typeOfExpr expr venv tenv)
  case actualType of
    Left (err::(E.SomeException)) -> assertFailure (
      (showSp pos) ++ ": " ++ (show err))
    Right (exprType) -> do
      assertBool ((showSp pos) ++ ": type mismatch, " ++ 
                  (renderType exprType) ++ " is not a subtype of " ++ 
                  (renderType expectedType)) 
                 (exprType `isSubTypeOf` expectedType)


assertTypeError pos expr venv tenv = do
  result <- E.try (typeOfExpr expr venv tenv)
  case result of
    Left (err::(E.SomeException)) -> return () -- error expected
    Right (exprType) -> assertFailure (
      (showSp pos) ++ ": expected fail, got: " ++ (renderType exprType))


assertTypeSuccess pos expr venv tenv = do
  result <- E.try (typeOfExpr expr venv tenv)
  case result of
    Left (err::(E.SomeException)) -> assertFailure ((showSp pos) ++ ": expected success, got: " ++ (show $ err)) 
    Right exprType -> return () -- success expected


parseTestCase venv tenv isSubTypeOf = do
  pos <- getPosition
  expr <- parseExpression
  let typeOK = do
        expectedType <- parseType -- requires a prefixed ::
        return $ TestCase (assertType pos expr expectedType venv tenv 
                                      isSubTypeOf)
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
   
  typeOK <|> (try typeError) <|> typeSuccess


parseAllTests venv tenv isSubTypeOf = do
  whiteSpace
  tests <- parseTestCase venv tenv isSubTypeOf `endBy` semi
  eof -- ensure the whole file parses
  return tests
  
--readTestFile :: FilePath -> IO Test
readTestFile venv tenv isSubTypeOf path = do
  result <- parseFromFile (parseAllTests venv tenv isSubTypeOf) path
  case result of
    -- Reporting the parse error is deferred until the test is run.
    Left err -> return $ TestCase (assertFailure (show err))
    Right tests -> return $ TestList tests
    

getTestPaths :: IO [String]
getTestPaths = do
  data_ <- getDataDir
  args <- getArgs
  case args of
    [] -> getPathsWithExtension ".js" (data_ </> "tests" </> "type-check")
    otherwise -> return $ map ((data_ </> "tests" </> "type-check") </>) args


main = do
  testPaths <- getTestPaths
  domTypeEnv <- makeInitialEnv
  (venv, tenv) <- loadCoreEnv M.empty domTypeEnv []
  let isRight (Right _) = True
      isRight _ = False
  let isSubTypeOf a b = isRight $ isSubType tenv [] a b
  testCases <- mapM (readTestFile venv (M.union domTypeEnv tenv) isSubTypeOf) 
                    testPaths
  runTest (TestList testCases)
