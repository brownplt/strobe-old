#!/usr/bin/env runhaskell
import Distribution.Simple
import qualified Data.List as L
import System.Directory
import System.Process (runCommand,waitForProcess)
import Data.Char (toLower)

isHaskellFile file = ".lhs" `L.isSuffixOf` file || ".hs" `L.isSuffixOf` file

moduleName file = L.takeWhile (\ch -> ch /= '.') file

isRequested :: [String] -> String -> Bool
isRequested requestedTests test = 
  (map toLower test) `elem` (map (map toLower) requestedTests)	

testMain args _ _ _ = do
  files <- getDirectoryContents "tests"
  let tests = filter isHaskellFile files
  let testModules = if null args
                      then map moduleName tests
                      else filter (isRequested args) (map moduleName tests)
  let testFuncs = map (++ ".main") testModules
  let testExpr = "sequence [ " ++ concat (L.intersperse "," testFuncs) ++ 
                 " ] >>= \\cases -> runTestTT (TestList cases)"
  let moduleLine = concat (L.intersperse " " testModules)
  let cmd = "cd tests && TypedJavaScript_datadir=../data " ++
            "ghc  -XNoMonomorphismRestriction -fglasgow-exts " ++
            "-fwarn-incomplete-patterns -package HUnit " ++
            "-package parsec-2.1.0.1 " ++
            "-i../src:../dist/build/autogen -e \"" ++ 
            testExpr ++ " >> return ()\" " ++ moduleLine
  handle <- runCommand cmd
  waitForProcess handle
  putStrLn "Testing complete.  Errors reported above (if any)."


main = defaultMainWithHooks (simpleUserHooks { runTests = testMain })
