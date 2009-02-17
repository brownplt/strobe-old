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
import TypedJavaScript.Contracts (encapsulateTypedModule)

import TypedJavaScript.Test

assertSucceeds :: SourcePos 
               -> Statement SourcePos
               -> JS.Statement SourcePos
               -> Assertion
assertSucceeds pos tjs js = do
  env <- typeCheck [tjs]
  tjs' <- encapsulateTypedModule (eraseTypesStmts [tjs]) env
  let str = "var window = { };\n" ++ render (JS.pp $ JS.BlockStmt pos [tjs',js])
  r <- rhino (sourceName pos) (B.pack str)
  case r of
    Right stdout -> return ()
    Left stderr  -> assertFailure $ "Error from Rhino on " ++ show pos ++ 
                                    "\n" ++ (B.unpack stderr)

assertBlames :: SourcePos 
             -> String -- ^guilty party
             -> Statement SourcePos
             -> JS.Statement SourcePos
             -> Assertion
assertBlames pos blamed tjs js = do
  let regexp = B.pack $ blamed ++ " violated the contract"
  env <- typeCheck [tjs]
  tjs' <- encapsulateTypedModule (eraseTypesStmts [tjs]) env
  let str = "var window = { };\n" ++ render (JS.pp $ JS.BlockStmt pos [tjs',js])
  r <- rhino (sourceName pos) (B.pack str)
  case r of
    Right stdout -> assertFailure $ "expected error at " ++ show pos ++
                                    "; stdout printed " ++ (B.unpack stdout)
    Left stderr  -> case stderr =~ regexp of
      True -> return ()
      False -> assertFailure $ "expected contract violation blaming " ++ 
                               blamed ++ " at " ++ show pos ++
                               "; stderr printed " ++ (B.unpack stderr)

parseTestCase :: CharParser st Test
parseTestCase = do
  pos <- getPosition
  let succeeds = do
        reserved "succeeds"
        tjs <- parseBlockStmt
        js <- JS.parseBlockStmt
        return $ TestCase (assertSucceeds pos tjs js)
      blames = do
        reserved "blames"
        blamed <- stringLiteral
        tjs <- parseBlockStmt
        js <- JS.parseBlockStmt
        return $ TestCase (assertBlames pos blamed tjs js)
  succeeds <|> blames
  
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
