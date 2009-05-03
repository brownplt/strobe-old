-- |A parser for IDL, written by eyeballing the W3C DOM IDLs.  This does not
-- follow any specification and is completely incorrect.
module BrownPLT.IDL.Parser where

import Text.ParserCombinators.Parsec
import Control.Monad
import Data.Maybe

import BrownPLT.IDL.Lexer
import BrownPLT.IDL.Syntax


type_ :: CharParser st Type
type_ = do
  let int = do
        optional (reserved "unsigned")
        reserved "int" <|> reserved "short"
          <|> (reserved "long" >> optional (reserved "long"))
        return TInt
  let bool = do
        reserved "boolean"
        return TBool
  let void = do
        reserved "void"
        return TVoid
  let id = do
        v <- identifier
        return (TId v)
  int <|> bool <|> void <|> id


value :: CharParser st Value
value = do
  n <- integer
  return (VInt n)


-- flattens modules
module_ :: CharParser st [Definition]
module_ = do
  reserved "module"
  identifier
  definitions


definitions :: CharParser st [Definition]
definitions = liftM catMaybes (braces (definition `sepEndBy` semi))


-- |Returns 'Nothing' when the definition is ignored.
-- Ignores typedef, exceptions are treated as interfaces, all method arguments
-- must be in.
-- Further assumptions are should be evident by the definition of 'Definition'.
definition :: CharParser st (Maybe Definition)
definition = do
  let typedef = do
        reserved "typedef"
        type_
        type_
        return Nothing
  let interface = do
        reserved "interface"
        name <- identifier
        let inherit = do
              colon
              parent <- identifier
              body <- definitions
              return (Just $ Interface name (Just parent) body)
        let noInherit = do
              body <- definitions
              return (Just $ Interface name Nothing body)
        let forward = do
              return Nothing
        inherit <|> noInherit <|> forward
  let exception = do
        reserved "exception"
        name <- identifier
        let attr = do
              t <- type_
              v <- identifier
              return (Attr False t v)
        attrs <- braces (attr `sepEndBy` semi)
        return (Just $ Interface name Nothing attrs)
  let attr = do
        readOnly <- (reserved "readonly" >> return True) <|> (return False)
        reserved "attribute"
        t <- type_
        v <- identifier
        return (Just $ Attr readOnly t v)
  let const = do
        reserved "const"
        t <- type_
        v <- identifier
        reservedOp "=" 
        val <- value
        return (Just $ Const t v val)
  let arg = do -- for method
        reserved "in"
        t <- type_
        v <- identifier
        return (t, v)
  let method = do
        t <- type_
        name <- identifier
        args <- parens (arg `sepBy` comma)
        let raises = do
              reserved "raises"
              parens (identifier `sepBy` comma)
              return ()
        optional raises
        return (Just $ Method t name args)
  typedef <|> interface <|> exception <|> attr <|> const <|> method


allDefinitions :: CharParser st [Definition]
allDefinitions = do
  whiteSpace
  defs <- liftM catMaybes (definition `sepEndBy` semi)
  eof
  return defs


-- |Removes lines beginning with #
preprocess :: String -> String
preprocess = unlines . (map unPound) . lines
  where unPound ('#':_) = "" -- instead of filtering, preserves line numbers
        unPound s = s

parseIDL :: SourceName -- ^source name
         -> String -- ^character stream
         -> Either ParseError [Definition]
parseIDL srcName inStream = parse allDefinitions srcName (preprocess inStream)


parseIDLFromFile :: SourceName
                 -> IO [Definition]
parseIDLFromFile srcPath = do
  inStream <- readFile srcPath
  case parseIDL srcPath inStream of
    Left err -> fail $ "BrownPLT.IDL.Parser.parseIDLFromFile: " ++ show err
    Right idl -> return idl
