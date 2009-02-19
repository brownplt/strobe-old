module TypedJavaScript.Test
  ( pretty
  , parse
  , parseJavaScriptFromFile
  , getPathsWithExtension
  , isJsFile
  , isTjsFile
  , getJsPaths
  , getTjsPaths
  , rhino
  , RhinoService, feedRhino, startRhinoService
  ) where

import qualified Data.List as L
import Data.List (isSuffixOf)
import Data.Maybe (catMaybes)
import qualified Data.Foldable as Foldable
import Data.Foldable (Foldable)
import Control.Monad
import qualified Data.Map as M

import System.Process
import System.Directory
import System.FilePath
import System.IO
import System.Exit
import qualified Data.ByteString.Char8 as B
import System.IO.Unsafe (unsafePerformIO)
import Data.Generics
import Test.HUnit

import Text.PrettyPrint.HughesPJ (render, vcat)
import Text.ParserCombinators.Parsec (ParseError,sourceName,sourceLine,
  sourceColumn,errorPos,SourcePos)
import TypedJavaScript.PrettyPrint (pp)
import TypedJavaScript.Syntax
import TypedJavaScript.Parser (parseScriptFromString,parseJavaScriptFromFile,
  ParsedStatement)

pretty :: [ParsedStatement] -> String
pretty stmts = render $ vcat $ map pp stmts

isPrettyPrintError :: ParseError -> Bool
isPrettyPrintError pe = 
  "(PRETTY-PRINTING)" `isSuffixOf` sourceName (errorPos pe)

parse :: FilePath -> String -> [ParsedStatement]
parse src str = case parseScriptFromString src str of
  Left err | isPrettyPrintError err -> 
               (unsafePerformIO $ putStrLn str) `seq` error (show err)
           | otherwise -> error (show err)
  Right (Script _ stmts) -> stmts

isJsFile :: String -> Bool
isJsFile = (== ".js") . takeExtension 

isTjsFile :: String -> Bool
isTjsFile = (== ".tjs") . takeExtension

getJsPaths :: FilePath -> IO [FilePath]
getJsPaths dpath = do
    exists <- doesDirectoryExist dpath
    paths <- if exists then getDirectoryContents dpath else return []
    return [dpath </> p | p <- paths, isJsFile p]

getTjsPaths :: FilePath -> IO [FilePath]
getTjsPaths dpath = do
    exists <- doesDirectoryExist dpath
    paths <- if exists then getDirectoryContents dpath else return []
    return [dpath </> p | p <- paths, isTjsFile p]

-- |The extension must include the leading period.
getPathsWithExtension :: String -> FilePath -> IO [FilePath]
getPathsWithExtension extension parentDirectory = do
  exists <- doesDirectoryExist parentDirectory
  case exists of
    False -> return []
    True -> do
      allPaths <- getDirectoryContents parentDirectory
      return [ parentDirectory</>path | path <- allPaths, 
                                        takeExtension path == extension ]

commandIO :: FilePath -- ^path of the executable
          -> [String] -- ^command line arguments
          -> B.ByteString  -- ^stdin
          -> IO (Either B.ByteString B.ByteString) -- ^stderr or stdout
commandIO path args stdinStr = do
  let cp = CreateProcess (RawCommand path args) Nothing Nothing CreatePipe
                         CreatePipe CreatePipe True
  (Just hStdin, Just hStdout, Just hStderr, hProcess) <- createProcess cp
  B.hPutStr hStdin stdinStr
  stdoutStr <- B.hGetContents hStdout
  stderrStr <- B.hGetContents hStderr
  exitCode <- waitForProcess hProcess
  case exitCode of
    ExitSuccess -> return (Right stdoutStr)
    ExitFailure n -> return (Left stderrStr)

rhino :: FilePath        -- ^Path to the file
      -> B.ByteString    -- ^JavaScript source
      -> IO (Either B.ByteString B.ByteString) -- ^Result from Rhino
rhino path {- not used -} src = do
  commandIO "/usr/bin/env" 
    ["java", "-classpath", "rhino.jar",
     "org.mozilla.javascript.tools.shell.Main"]
    src

--rhinoservice
data RhinoService = RhinoService Handle Handle Handle ProcessHandle

startRhinoService :: IO RhinoService
startRhinoService = do
  let cp = CreateProcess (RawCommand "/usr/bin/env" 
                                     ["java", "-classpath", 
                                      "tests/rhino.jar:.:tests/", "RhinoService"]) 
                         Nothing Nothing CreatePipe CreatePipe CreatePipe True
  (Just hStdin, Just hStdout, Just hStderr, hProcess) <- createProcess cp
  return $ RhinoService hStdin hStdout hStderr hProcess

feedRhino :: RhinoService -> B.ByteString -> IO B.ByteString
feedRhino (RhinoService hStdin hStdout hStderr hProcess) input = do
  putStrLn $ "Writing : " ++ show (B.pack $ show ((B.length input) + 1))
  B.hPutStrLn hStdin $ B.pack $ show ((B.length input) + 1)
  putStrLn $ "Writing : " ++ show input
  B.hPutStrLn hStdin input
  stdoutStr <- B.hGetContents hStdout
  stderrStr <- B.hGetContents hStderr
  exitCode <- waitForProcess hProcess
  case exitCode of
    ExitSuccess -> putStrLn $ "SUCCESS" ++ show stdoutStr ++ show stderrStr
    ExitFailure n -> putStrLn $ "FAIL"  ++ show stdoutStr ++ show stderrStr
  outputlenBStr <- B.hGetLine hStderr
  let outputlenStr = take ((B.length outputlenBStr)-1) (B.unpack outputlenBStr)
  let outputlen = read outputlenStr::Int
  B.hGet hStdout outputlen