module TypedJavaScript.Test
  ( pretty
  , parse
  , parseJavaScriptFromFile
  , isJsFile
  , isTjsFile
  , getJsPaths
  , getTjsPaths
  ) where

import qualified Data.List as L
import Data.List ( isSuffixOf )
import Data.Maybe (catMaybes)
import qualified Data.Foldable as Foldable
import Data.Foldable (Foldable)
import Control.Monad
import qualified Data.Map as M

import System.Directory
import System.FilePath
import System.IO.Unsafe ( unsafePerformIO )
import Data.Generics
import Test.HUnit

import Text.PrettyPrint.HughesPJ ( render, vcat )
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

