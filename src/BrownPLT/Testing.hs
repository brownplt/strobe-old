module BrownPLT.Testing 
  ( runTest
  ) where

import Text.Printf
import System.IO
import Test.HUnit.Base
import System.Console.ANSI


reportStart :: ReportStart us
reportStart _ us = return us


reportError :: ReportProblem us
reportError msg s us = do
  hSetSGR stderr [SetUnderlining SingleUnderline]
  hPutStr stderr "Error:"
  hSetSGR stderr [SetUnderlining NoUnderline]
  hPutStrLn stderr (' ':msg)
  return us


reportFailure :: ReportProblem us
reportFailure msg s us = do
  hSetSGR stderr [SetUnderlining SingleUnderline]
  hPutStr stderr "Failed:"
  hSetSGR stderr [SetUnderlining NoUnderline]
  hPutStrLn stderr (' ':msg)
  return us


runTest :: Test -> IO ()
runTest test = do
  (counts, _) <- performTest reportStart reportError reportFailure () test
  hPutStrLn stderr $ printf "Cases: %d Tried: %d Errors: %d Failures: %d"
                            (cases counts) (tried counts) (errors counts)
                            (failures counts)
