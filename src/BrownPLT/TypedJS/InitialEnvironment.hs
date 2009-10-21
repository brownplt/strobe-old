-- |Uses W3C IDL files to create the initial environment for Typed JavaScript
-- programs.
module BrownPLT.TypedJS.InitialEnvironment
  ( loadIDLs
  ) where

import Paths_TypedJavaScript
import System.Directory
import System.FilePath
import qualified Data.Map as M
import qualified BrownPLT.IDL as IDL
import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.TypeDefinitions
import BrownPLT.TypedJS.TypeTheory
import BrownPLT.TypedJS.Infrastructure
import BrownPLT.TypedJS.Syntax (TopLevel (..), unId, Id (..))
import BrownPLT.TypedJS.Parser (parseTypedJavaScript)
import Control.Monad.Error


type IDLs = [IDL.Definition]


-- |These files must be in order.
idlFiles :: [FilePath]
idlFiles = 
  [ "idl" </> "dom.idl"
  , "idl" </> "events.idl"
  , "idl" </> "html.idl"
  , "idl" </> "xmlhttprequest.idl"
  , "idl" </> "views.idl"
  , "idl" </> "window.idl"
  , "idl" </> "typedjs-extras.idl"
  , "idl" </> "typedjs-core.idl"
  ]

-- |Search for typedef in the DOM IDLs.  We need an entry for each typedef.
extras :: [(String, Type)]
extras = 
  [ ("DOMString", rStrType)
  , ("float", rDoubleType)
  , ("double", rDoubleType)
  , ("DOMObject", TObject "Object" [] [])
  , ("DOMUserData", TAny)
  , ("DOMTimeStamp", rIntType)
  , ("AnyFunction", TArrow TAny (ArgType [] (Just TAny)) TAny)
  , ("WindowLocation",
     TObject "Object" [] [
       ("search", True, rStrType)])
  ]

parseIDLType :: IDL.Type -> Type
parseIDLType t = case t of
  IDL.TInt -> rIntType
  IDL.TBool -> boolType
  IDL.TVoid -> undefType
  IDL.TId id -> case lookup id extras of
    Just t -> t
    Nothing -> TObject id [] []


-- |Assumes all names are unique in the list of members.
-- Makes methods and constants readonly in the type system.
fieldsFromIDL :: String -> [IDL.Definition] -> TypeCheck [Field]
fieldsFromIDL self members = mapM field members
  where field (IDL.Const t v _) = return (v, True, parseIDLType t)
        field (IDL.Attr isReadOnly t v) = return (v, isReadOnly, parseIDLType t)
        field (IDL.Method ret v args) = 
          return (v, True, 
                  TArrow (TObject self [] [])
                         -- formal arguments are named, so fst
                         (ArgType (map (parseIDLType.fst) args) Nothing)
                         (parseIDLType ret))
        field def = 
          fail $ "BrownPLT.TypedJS.InitialEnvironment.objectFromIDL: \
                  \unexpected " ++ show def


bindingFromIDL :: IDL.Definition 
               -> TypeCheck a
               -> TypeCheck a
bindingFromIDL def cont = case def of
  IDL.Const t v _ -> extendEnv v (parseIDLType t) cont
  IDL.Interface v Nothing body -> do
    fields <- fieldsFromIDL v body
    ty <- canonize (TObject v [] fields)
    newRootBrand ty
    extendEnv v (TConstr v [] TAny ty) cont -- TODO: this is a hack (also below)
  IDL.Interface v (Just parent) body -> do
    fields <- fieldsFromIDL v body
    ty <- getBrand parent
    case ty of
      (TObject _ args fields') -> do
        ty' <- canonize (TObject v [] (overrideFields fields fields'))
        newBrand v ty' (TObject parent args fields')
        extendEnv v (TConstr v [] TAny ty') cont
      otherwise ->
        fail $ "bindingFromIDL: getBrand returned " ++ show ty
  otherwise -> fail $ "bindingFromIDL: unexpected " ++ show def


withIDLs :: IDLs
         -> TypeCheck a
         -> TypeCheck a
withIDLs []         cont = cont
withIDLs (def:defs) cont = bindingFromIDL def (withIDLs defs cont)


loadDecls [] cont = cont
loadDecls (tl:tls) cont  = case tl of
  ImportConstrStmt p (Id _ brand) True ty -> do
    newBrand brand (getConstrObj ty) (TObject "Object" [] [])
    ty <- desugarType noPos ty
    extendEnv brand (lcType ty) cont
  ImportStmt p name True ty -> do
    extendEnv (unId name) ty (loadDecls tls cont)
  otherwise -> fail $ printf "error loading preamble.jst: unexpected %s"
    (show tl)


loadIDLs :: IO InitialStoreEnv
loadIDLs = do
  dataDir <- getDataDir
  let idlPaths = map (dataDir </>) idlFiles
  let corePath = dataDir </> "preamble.jst"
  idls <- liftM concat (mapM IDL.parseIDLFromFile idlPaths)
  src <- readFile corePath
  let stx = parseTypedJavaScript corePath src
  let m = withIDLs idls $ loadDecls stx getInitialStoreEnv
  case runEmptyTypeCheck m of
    Left s -> fail $ "error loading IDLs: " ++ s
    Right st -> return st
