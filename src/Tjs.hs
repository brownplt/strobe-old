module Main where

import System.Console.GetOpt
import System.Environment
import System.IO
import System.Exit

import qualified Data.Graph.Inductive as G
import qualified Data.GraphViz as GV

-- import BrownPLT.TypedJS.InitialEnvironment
import BrownPLT.JavaScript.Analysis
import BrownPLT.JavaScript.Analysis.ANFPrettyPrint (prettyANF, prettyLit)
import BrownPLT.JavaScript.Analysis.Intraprocedural
import BrownPLT.TypedJS.Prelude
import qualified Data.Map as M
import Text.PrettyPrint.HughesPJ (render, vcat)
import qualified BrownPLT.JavaScript as JS
import BrownPLT.TypedJS.Syntax
import BrownPLT.TypedJS.Parser
import BrownPLT.TypedJS.Lexer
-- import BrownPLT.TypedJS.Contracts
import BrownPLT.TypedJS.TypeErasure
import BrownPLT.TypedJS.PrettyPrint
import BrownPLT.TypedJS.TestParser
import Test.HUnit
import BrownPLT.Testing
import BrownPLT.TypedJS.TypeCheck
import BrownPLT.TypedJS.RuntimeAnnotations

pretty :: [ParsedStatement] -> String
pretty = renderStatements

data Flag
  = Help
  | ANF
  | TypeCheck
  | Graphs
  | PrintType String
  | InteractiveTesting
  | Testing
  | Annotated
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
  , Option [] ["testing"] (NoArg Testing)
      "reads in multiple test files"
  , Option [] ["annotated"] (NoArg Annotated)
      "prints the program annotated with runtime type information"
  ]





type Action = [Flag] -> [String] -> IO ()


typeCheckAction :: Action
typeCheckAction [] [path] = do
  src <- readFile path
  let (_, script) = parseTypedJavaScript path src
  case typeCheck script of
    Right () -> putStrLn "Type-checking successful."
    Left errs -> putStrLn errs
typeCheckAction _ _ = fail "invalid command-line arguments"


testingAction [] paths = do
  tests <- mapM parseTestFile paths
  runTest (TestList tests)
testingAction _ _ = fail "invalid command-line arguments"


annotatedAction [path] = do
  src <- readFile path
  let (_, script) = parseTypedJavaScript path src
  putStrLn "Successfully parsed..."
  case runtimeAnnotations M.empty (BlockStmt noPos script) of
    Left err -> putStrLn err
    Right script' -> putStrLn (pretty [script'])
annotatedAction _ = fail "invalid command-line arguments"


{-

getAction (ANF:args) = return (RequireInput action, args) where
  action (_, prog) = do
    let (topDecls, anfProg) = toANF (simplify (eraseTypes prog))
    putStrLn (prettyANF anfProg)
getAction (Graphs:args) = return (RequireInput action, args) where
  action (_, prog) = do
    let anf = toANF (simplify (eraseTypes prog))
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
getAction ((PrintType name):args) = return (RequireInput action, args) where
  action (toplevs, prog) = do
    domTypeEnv <- makeInitialEnv
    (venv, tenv) <- loadCoreEnv M.empty domTypeEnv toplevs
    case M.lookup name tenv of
      Just t -> putStrLn (renderType t)
      Nothing -> fail $ printf "%s is not a type name" name
-}

main = do
  args <- getArgs
  let (permutedArgs, files, errors) = getOpt Permute options args
  unless (null errors) $ do
    mapM_ (hPutStrLn stderr) errors
    exitFailure

  case sort permutedArgs of
    [] -> typeCheckAction [] files
    (TypeCheck:args) -> typeCheckAction args files
    (Testing:args) -> testingAction args files
    [Annotated] -> annotatedAction files
    [Help] -> do
      putStrLn "Typed JavaScript Compiler"
      putStrLn (usageInfo "Usage: jst [OPTION ...] [file]" options)
    otherwise -> do
      fail "invalid command-line arguments (try --help)"
