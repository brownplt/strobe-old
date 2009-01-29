module Main where

import TypedJavaScript.Syntax
import TypedJavaScript.Parser
import TypedJavaScript.Lexer

import Text.PrettyPrint.HughesPJ ( render, vcat )
import TypedJavaScript.PrettyPrint (pp)

pretty :: [ParsedStatement] -> String
pretty stmts = render $ vcat $ map pp stmts

main = do
  strscript <- getContents
  putStrLn $ show $ parseString strscript
  putStrLn ""
  putStrLn "Pretty-printed version:"
  putStrLn "-----------------------"
  putStrLn $ pretty $ parseString strscript

