module Main where

import System.Console.GetOpt
import System.Environment
import System.IO
import System.Exit

import qualified Data.Graph.Inductive as G
import qualified Data.GraphViz as GV

import BrownPLT.JavaScript.Analysis
import BrownPLT.JavaScript.Analysis.ANFPrettyPrint (prettyANF, prettyLit)
import BrownPLT.JavaScript.Analysis.Intraprocedural
import TypedJavaScript.Prelude
import qualified Data.Map as M
import Text.PrettyPrint.HughesPJ (render, vcat)
import qualified BrownPLT.JavaScript as JS
import TypedJavaScript.Syntax
import TypedJavaScript.Parser
import TypedJavaScript.Lexer
import TypedJavaScript.Contracts
import TypedJavaScript.TypeErasure
import TypedJavaScript.PrettyPrint
import TypedJavaScript.TypeCheck


pretty :: [ParsedStatement] -> String
pretty = renderStatements

data Flag
  = Help
  | ANF
  | TypeCheck
  | Graphs
  | PrintType String
  deriving (Eq, Ord)

options :: [OptDescr Flag]
options =
  [ Option ['h'] ["help"] (NoArg Help)
      "display this help message"
  , Option ['t'] ["type-check"] (NoArg TypeCheck)
      "type-check the program"
  , Option ['f'] ["anf"] (NoArg ANF)
      "print the program in ANF"
  , Option ['g'] ["graphs"] (NoArg Graphs)
      "print the interprocedural graphs of the program"
  , Option ['y'] ["type"] (ReqArg PrintType "NAME")
      "prints the type named NAME"
  ]

checkHelp (Help:_) = do
  putStrLn "Typed JavaScript Compiler"
  putStrLn (usageInfo "Usage: jst [OPTION ...] [file]" options)
  putStrLn ""
  putStrLn "If you do not specify any options, the type-checker will run."
  putStrLn "If you do not specify a filename, the program will read from"
  putStrLn "standard input."
  exitSuccess
checkHelp _ = return ()

getInput [] = return (stdin, "stdin")
getInput [file] = do
  h <- openFile file ReadMode
  return (h, file)
getInput files = do
  hPutStrLn stderr "multiple input files are not yet supported"
  exitFailure

data Action = RequireInput ([Statement SourcePos] -> IO ())
            | NoInput (IO ())

getAction (ANF:args) = return (RequireInput action, args) where
  action prog = do
    let (topDecls, anfProg) = jsToCore (simplify (eraseTypes prog))
    putStrLn (prettyANF anfProg)
getAction (TypeCheck:args) = return (RequireInput action, args) where
  action prog = do
    typeCheck prog
    putStrLn "Type-checking successful."
getAction (Graphs:args) = return (RequireInput action, args) where
  action prog = do
    let anf = jsToCore (simplify (eraseTypes prog))
    let (clusterFn,gr) = clusteredIntraproceduralGraphs anf
    let clusterAttrFn :: Int -> [GV.Attribute] -- avoid ambiguity
        clusterAttrFn = const []
    let edgeFn (_, _, Nothing) = []
        edgeFn (_, _, Just lit) = [GV.Label (prettyLit lit)]
    let dot = GV.clusterGraphToDot gr [] -- attributes
                (\(n,l) -> GV.C (clusterFn n) (GV.N (n,l))) -- clustering
                clusterAttrFn
                (\(n,s) -> [GV.Label (show s)]) -- node atributes
                edgeFn -- edge attributes
    hPutStrLn stdout (show dot)
getAction ((PrintType name):args) = return (NoInput action, args) where
  action = do
    t <- getType name
    putStrLn (renderType t)
getAction args = return (RequireInput action, args) where
  action prog = do
    typeCheck prog
    putStrLn "Type-checking successful."

main = do
  args <- getArgs
  let (permutedArgs, files, errors) = getOpt Permute options args
  unless (null errors) $ do
    mapM_ (hPutStrLn stderr) errors
    exitFailure

  let args = sort permutedArgs
  checkHelp args

  (inputHandle, inputName) <- getInput files
  (action, args) <- getAction args

  unless (null args) $ do
    hPutStrLn stderr "superfluous arguments"
    exitFailure

  case action of
    RequireInput action -> do
      str <- hGetContents inputHandle
      let script = parseTypedJavaScript inputName str
      action script
    NoInput action -> action
