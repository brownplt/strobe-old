module Main where

import qualified Data.Map as M
import Text.PrettyPrint.HughesPJ (render, vcat)

import qualified BrownPLT.JavaScript as JS

import TypedJavaScript.Syntax
import TypedJavaScript.Parser
import TypedJavaScript.Lexer
import TypedJavaScript.Contracts
import TypedJavaScript.TypeErasure
import TypedJavaScript.PrettyPrint (pp)
import TypedJavaScript.TypeCheck


pretty :: [ParsedStatement] -> String
pretty stmts = render $ vcat $ map pp stmts

main = do
  str <- getContents
  let stmts = parseString str
  env <- typeCheck stmts
  putStrLn "Typecheck OK"
