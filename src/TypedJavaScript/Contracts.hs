-- |Converts types to contracts.
module TypedJavaScript.Contracts
  ( toContract
  , toInterface
  , encapsulate
  , encapsulateTypedModule
  , getContractsLib
  ) where

import TypedJavaScript.Prelude
import qualified Data.Map as M
import System.FilePath

import Paths_TypedJavaScript -- generated by Cabal

import BrownPLT.JavaScript.Contracts (Contract (..), getContractLibraryPath,
  InterfaceItem (..), compile)
import TypedJavaScript.Types (Env)
import TypedJavaScript.Syntax (Type (..))
import qualified BrownPLT.JavaScript as JavaScript

pos = noPos

-- |'toContract' assumes that the supplied type is closed and well-formed.
toContract :: Type -> Contract
{-toContract (TFunc (this:reqargs) maybeVararg result _) =
  FunctionContract noPos (map toContract reqargs) varargCtc (toContract result)
    where varargCtc = case maybeVararg of
                        Nothing -> Nothing
                        Just vararg -> Just (toContract vararg)-}
toContract (TId id) = 
  error $ "unbound identifier (" ++ show id ++ ") at " ++ show pos ++
          " while converting a type to a contract"
-- TODO: This should not be hard-coded.  Fix  when we enable
-- user-defined types. Also add nullable contract.
toContract (TApp constr args) = case (constr,args) of
  (TId "bool",[]) -> NamedContract pos "isBool"
  (TId "int",[]) -> NamedContract pos "isInt"
  (TId "string",[]) -> NamedContract pos "isString"
  (constr,args) -> error $ "toContract does not know " ++  show (constr,args)
--toContract (TNullable pos t) = FlatContract pos JavaScript
toContract x = error $ "toContract does not handle " ++ show x
--TODO: add arrayOf for objects with @[] in them.

-- |Converts a type environment (presumably, a top-level type-environment)
-- to a list of 'InterfaceItem's.
toInterface :: Env
            -> [InterfaceItem]
toInterface env = map toExport (M.toList env) where
  toExport (v,t) = InterfaceExport v noPos
                                   (toContract' t)
  toContract' Nothing = error "Contracts.hs : export without type"
  toContract' (Just (type_, vp)) = toContract type_

-- |Wraps a Typed JavaScript module (after type-erasure) with contracts. The
-- result is a single function-application statement.
encapsulate :: [JavaScript.Statement SourcePos] -- ^type-erased tJS
            -> Env -- ^environment (i.e. exports)
            -> [JavaScript.Statement SourcePos] -- ^contract library
            -> JavaScript.Statement SourcePos -- ^encapsulated module
encapsulate typeErasedStmts env contractLib = wrappedStmts where
  interface = toInterface env
  wrappedStmts = compile typeErasedStmts interface contractLib

getContractsLib = do
  contractLib <- getContractLibraryPath
  dataDir <- getDataDir
  let typedContractLib = dataDir</>"typedjs_contracts.js"
  contractLibStmts <- JavaScript.parseJavaScriptFromFile contractLib
  typedContractLibStmts <- JavaScript.parseJavaScriptFromFile typedContractLib
  return $ contractLibStmts ++ typedContractLibStmts

encapsulateTypedModule :: [JavaScript.Statement SourcePos]
                       -> Env
                       -> IO (JavaScript.Statement SourcePos)
encapsulateTypedModule typeErasedStmts env = do
  lib <- getContractsLib
  return $ encapsulate typeErasedStmts env lib
  
