-- |Contract test-cases.  The .js files in the contracts directory are
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

import TypedJavaScript.Syntax (Statement,showSp)
import TypedJavaScript.Lexer (semi,reservedOp, reserved,stringLiteral)
import TypedJavaScript.Parser (parseBlockStmt)


import TypedJavaScript.TypeChecker (typeCheck)
import TypedJavaScript.TypeErasure (eraseTypesStmts)
import TypedJavaScript.Contracts (encapsulate, 
  encapsulateTypedModule, getContractsLib)

import TypedJavaScript.Test

--TODO: do what old rhino did for sucess/fail
import System.Exit 

--TODO: these can be considered type-check tests, too?
runTest rs pos tjs js shouldEncaps = do
  --env <- typeCheck [tjs] --TODO: print line numbers for type-check errors
  result <- E.try $ typeCheck [tjs]
  case result of
    Left (err::(E.SomeException)) -> return $ Left $ assertFailure 
      ((showSp pos) ++ ": failed to type-check: " ++ (show $ err))
    Right env -> return $ Right $ do
      case shouldEncaps of
        True -> do
          tjs' <- return $ encapsulate (eraseTypesStmts [tjs]) env []
          let str = render (JS.pp $ JS.BlockStmt pos [tjs',js])
          feedRhino rs (B.pack str) 
        False -> do
          tjs' <- return $ eraseTypesStmts [tjs]
          let str = render (JS.pp $ JS.BlockStmt pos (tjs' ++ [js]))
          feedRhino rs (B.pack str)

assertSucceeds :: RhinoService 
               -> SourcePos 
               -> Statement SourcePos
               -> JS.Statement SourcePos
               -> Bool
               -> Assertion
assertSucceeds rs pos tjs js shouldEncaps = do
  --possible exception names so far: JavaScriptException, EcmaError
  --possible exception types so far: Exception, TypeError
  let regexp = B.pack $ "org.mozilla.javascript.[a-zA-Z0-9_]*: "
  retval <- runTest rs pos tjs js shouldEncaps
  case retval of
    Left failed -> failed
    Right retstr' -> do
      retstr <- retstr'
      case retstr =~ regexp of
        True -> assertFailure $ (showSp pos) ++ ": Expected success, but an" ++ 
                                " exception was printed:\n" ++ B.unpack retstr
        False -> return ()                            

assertBlames :: RhinoService 
             -> SourcePos 
             -> String -- ^guilty party
             -> Statement SourcePos
             -> JS.Statement SourcePos
             -> Bool
             -> Assertion
assertBlames rs pos blamed tjs js shouldEncaps = do
  let regexp = B.pack $ blamed ++ " violated the contract"
  retval <- runTest rs pos tjs js shouldEncaps
  case retval of
    Left fail -> fail
    Right retstr' -> do
      retstr <- retstr'
      case retstr =~ regexp of
        True -> return ()
        False -> assertFailure $ 
          (showSp pos) ++ ": Expected contract violation blaming " ++ 
          blamed ++ " at " ++ show pos ++ "; rhino returned " ++ 
          B.unpack retstr

closeRhinoTest :: RhinoService -> Assertion
closeRhinoTest rs = do
  code <- stopRhino rs
  case code of
    ExitSuccess -> assertBool "Rhino succeed" True
    ExitFailure n -> assertFailure $ "Rhino fail, exit code: " ++ (show n)

parseTestCase :: RhinoService -> CharParser st Test
parseTestCase rs = do
  pos <- getPosition
  shouldEncaps <- (reserved "dontencapsulate" >> return False) <|>
                  (return True)
  let succeeds = do
        reserved "succeeds"
        tjs <- parseBlockStmt
        js <- JS.parseBlockStmt
        return $ TestCase (assertSucceeds rs pos tjs js shouldEncaps)
      blames = do
        reserved "blames"
        blamed <- stringLiteral
        tjs <- parseBlockStmt
        js <- JS.parseBlockStmt
        return $ TestCase (assertBlames rs pos blamed tjs js shouldEncaps)
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
  let str = "var window = { };\n" ++ render 
              (JS.pp $ JS.BlockStmt (initialPos "contractslib") lib)
  rez <- feedRhino rs $ B.pack str
  --TODO: check for exceptions for this initial feeding
  putStrLn $ "Contracts lib initialized, rhino returned: " ++ B.unpack rez
  
  testPaths <- getPathsWithExtension ".js" "contracts"
  testCases <- mapM (readTestFile rs) testPaths
  return (TestList $ testCases ++ [TestCase $ closeRhinoTest rs])
