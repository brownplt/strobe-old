module Main where

import TypedJavaScript.Syntax
import TypedJavaScript.Parser
import TypedJavaScript.Lexer

main = do
  strscript <- getContents
  putStrLn $ show $ parseString strscript

