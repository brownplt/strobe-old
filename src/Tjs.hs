module Main where

import TypedJavaScript.Syntax
import TypedJavaScript.Parser
import TypedJavaScript.Lexer

import Text.PrettyPrint.HughesPJ ( render, vcat )
import TypedJavaScript.PrettyPrint (pp)

import TypedJavaScript.Environment
import TypedJavaScript.TypeChecker

pretty :: [ParsedStatement] -> String
pretty stmts = render $ vcat $ map pp stmts

main = do
  strscript <- getContents
  let statements = parseString strscript
  putStrLn $ show $ statements
  putStrLn ""
  putStrLn "Pretty-printed version:"
  putStrLn "-----------------------"
  putStrLn $ pretty $ statements
  putStrLn "-----------------------"
  putStrLn "Global environment:"
  putStrLn "-----------------------"
  putStrLn $ show $ globalEnv $ statements
  putStrLn "Type checking..."
  success <- typeCheckStmts coreVarEnv coreTypeEnv statements
  putStrLn $ show $ success
  
