-- |Contract test-cases.  The .test files in the contracts directory are
-- parsed as:
--
-- tests ::= test ;
--         | test ; tests
--
-- test ::= succeeds { typedjs-statement* } { untypedjs-statement* }
--
-- Note that there is a trailing ';' at the end of a list of tests.
-- JavaScript-style comments are permitted in .test files.
module Contracts where

import Text.ParserCombinators.Parsec
import Text.PrettyPrint.HughesPJ (render)
import Test.HUnit
import qualified Control.Exception as E
import qualified Data.ByteString.Char8 as B

import qualified WebBits.JavaScript as JS

import TypedJavaScript.Syntax (Statement)
import TypedJavaScript.Lexer (semi,reservedOp, reserved)
import TypedJavaScript.Parser (parseBlockStmt)


import TypedJavaScript.TypeChecker (typeCheck)
import TypedJavaScript.TypeErasure (eraseTypesStmts)
import TypedJavaScript.Contracts (encapsulateTypedModule)

import TypedJavaScript.Test

{-
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
-}

assertSucceeds :: SourcePos 
               -> Statement SourcePos
               -> JS.Statement SourcePos
               -> Assertion
assertSucceeds pos tjs js = do
  env <- typeCheck [tjs]
  tjs' <- encapsulateTypedModule (eraseTypesStmts [tjs]) env
  let str = "var window = { };\n" ++ render (JS.pp $ JS.BlockStmt pos [tjs',js])
  rhino (sourceName pos) (B.pack str)
  return ()
               

parseTestCase :: CharParser st Test
parseTestCase = do
  pos <- getPosition
  let succeeds = do
        reserved "succeeds"
        tjs <- parseBlockStmt
        js <- JS.parseBlockStmt
        return $ TestCase (assertSucceeds pos tjs js)
  succeeds
  
readTestFile :: FilePath -> IO Test
readTestFile path = do
  result <- parseFromFile (parseTestCase `endBy` semi) path
  case result of
    -- Reporting the parse error is deferred until the test is run.
    Left err -> return $ TestCase (assertFailure (show err))
    Right tests -> return $ TestList tests
    
main = do
  testPaths <- getPathsWithExtension ".test" "contracts"
  testCases <- mapM readTestFile testPaths
  return (TestList testCases)
