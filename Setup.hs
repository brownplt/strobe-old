#!/usr/bin/env runhaskell
import Distribution.Simple
import System.Process (runCommand,waitForProcess)

testMain args _ _ _ = do
  let cmd = "TypedJavaScript_datadir=\"data\" \
            \./dist/build/typedjs-tests/typedjs-tests"
  handle <- runCommand cmd
  waitForProcess handle
  putStrLn "Testing complete.  Errors reported above (if any)."


main = defaultMainWithHooks (simpleUserHooks { runTests = testMain })
