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

import Text.Regex.Posix
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos
import Text.PrettyPrint.HughesPJ (render)
import Test.HUnit
import qualified Control.Exception as E
import qualified Data.ByteString.Char8 as B

import qualified WebBits.JavaScript as JS

import TypedJavaScript.Syntax (Statement)
import TypedJavaScript.Lexer (semi,reservedOp, reserved,stringLiteral)
import TypedJavaScript.Parser (parseBlockStmt)


import TypedJavaScript.TypeChecker (typeCheck)
import TypedJavaScript.TypeErasure (eraseTypesStmts)
import TypedJavaScript.Contracts (encapsulate, encapsulateTypedModule, getContractsLib)

import TypedJavaScript.Test

--TODO: do what old rhino did for sucess/fail
import System.Exit 

runTest rs pos tjs js = do
  env <- typeCheck [tjs]
  tjs' <- return $ encapsulate (eraseTypesStmts [tjs]) env []
  let str = "var window = { };\n" ++ render (JS.pp $ JS.BlockStmt pos [tjs',js])
  feedRhino rs (B.pack str) --rhino (sourceName pos) (B.pack str)

assertSucceeds :: RhinoService 
               -> SourcePos 
               -> Statement SourcePos
               -> JS.Statement SourcePos
               -> Assertion
assertSucceeds rs pos tjs js = do
  --possible exception names so far: JavaScriptException, EcmaError
  --possible exception types so far: Exception, TypeError
  let regexp = B.pack $ "org.mozilla.javascript.[a-zA-Z0-9_]*: "
  retstr <- runTest rs pos tjs js
  case retstr =~ regexp of
    True -> assertFailure $ "Expected success, but an exception was printed:\n" 
                            ++ B.unpack retstr
    False -> return ()                            

assertBlames :: RhinoService 
             -> SourcePos 
             -> String -- ^guilty party
             -> Statement SourcePos
             -> JS.Statement SourcePos
             -> Assertion
assertBlames rs pos blamed tjs js = do
  let regexp = B.pack $ blamed ++ " violated the contract"
  retstr <- runTest rs pos tjs js
  case retstr =~ regexp of
    True -> return ()
    False -> assertFailure $ "Expected contract violation blaming " ++ 
                             blamed ++ " at " ++ show pos ++ "; rhino returned " 
                             ++ B.unpack retstr

closeRhinoTest :: RhinoService -> Assertion
closeRhinoTest rs = do
  code <- stopRhino rs
  case code of
    ExitSuccess -> assertBool "Rhino succeed" True
    ExitFailure n -> assertFailure $ "Rhino didn't close, exit code " ++ (show n)

parseTestCase :: RhinoService -> CharParser st Test
parseTestCase rs = do
  pos <- getPosition
  let succeeds = do
        reserved "succeeds"
        tjs <- parseBlockStmt
        js <- JS.parseBlockStmt
        return $ TestCase (assertSucceeds rs pos tjs js)
      blames = do
        reserved "blames"
        blamed <- stringLiteral
        tjs <- parseBlockStmt
        js <- JS.parseBlockStmt
        return $ TestCase (assertBlames rs pos blamed tjs js)
  succeeds <|> blames
  
readTestFile :: RhinoService -> FilePath -> IO Test
readTestFile rs path = do
  result <- parseFromFile ((parseTestCase rs) `endBy` semi) path
  case result of
    -- Reporting the parse error is deferred until the test is run.
    Left err -> return $ TestCase (assertFailure (show err))
    Right tests -> return $ TestList tests
    
main = do
  rs <- startRhinoService

  --feed the rs the contracts library code
  lib <- getContractsLib
  let str = "var window = { };\n" ++ render (JS.pp $ JS.BlockStmt (initialPos "contractslib") lib)
  rez <- feedRhino rs $ B.pack str
  --TODO: check for exceptions
  putStrLn $ "Contracts lib initialized, rhino returned: " ++ B.unpack rez
  
  testPaths <- getPathsWithExtension ".test" "contracts"
  testCases <- mapM (readTestFile rs) testPaths
  return (TestList $ testCases ++ [TestCase $ closeRhinoTest rs])
