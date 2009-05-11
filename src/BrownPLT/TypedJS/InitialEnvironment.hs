-- |Uses W3C IDL files to create the initial environment for Typed JavaScript
-- programs.
module BrownPLT.TypedJS.InitialEnvironment
  ( makeInitialEnv
  ) where

import Paths_TypedJavaScript
import System.Directory
import System.FilePath
import qualified Data.Map as M
import qualified BrownPLT.IDL as IDL
import BrownPLT.IDL.RemoveInheritance
import TypedJavaScript.Prelude
import TypedJavaScript.Types
import TypedJavaScript.Syntax (Type (..), LatentPred (..), VP (..))


-- |The order in which these files are specified does not matter.
idlFiles :: [FilePath]
idlFiles = 
  [ "idl" </> "dom.idl"
  , "idl" </> "events.idl"
  , "idl" </> "html.idl"
  , "idl" </> "xmlhttprequest.idl"
  , "idl" </> "views.idl"
  , "idl" </> "window.idl"
  , "idl" </> "typedjs-extras.idl"
  ]

-- |Search for typedef in the DOM IDLs.  We need an entry for each typedef.
extras :: [(String, Type)]
extras = 
  [ ("DOMString", stringType)
  , ("DOMObject", TObject [])
  , ("DOMUserData", TAny)
  , ("DOMTimeStamp", intType)
  ]


parseIDLType :: IDL.Type -> Type
parseIDLType t = case t of
  IDL.TInt -> intType
  IDL.TBool -> boolType
  IDL.TVoid -> undefType
  IDL.TId id -> TId id


-- |Assumes all names are unique in the list of members.  This is guaranteed
-- by 'removeInheritance'.
--
-- Silently drops the readonly modifier on attributes.
objectFromIDL :: String -- ^self id
              -> [IDL.Definition] -- ^methods, attributes, etc.
              -> Type -- ^a TObject
objectFromIDL self members = TObject (map field members)
  where field (IDL.Const t v _) = (v, parseIDLType t)
        field (IDL.Attr isReadOnly t v) = (v, parseIDLType t)
        field (IDL.Method ret v args) = 
          (v, TFunc funcargstype rt LPNone)
            where formals = map parseIDLType (map fst args)
                  arguments = TAny -- TODO: het. arrays
                  rt = parseIDLType ret
                  argstype = (TSequence formals Nothing)
                  funcargstype = (TSequence ([(TId self), argstype]++
                                              formals)
                                             Nothing)
        field def = 
          error $ "BrownPLT.TypedJS.InitialEnvironment.objectFromIDL: \
                  \unexpected " ++ show def


bindingFromIDL :: IDL.Definition -> (String, Type)
bindingFromIDL def = case def of
  IDL.Const t v _ -> (v, parseIDLType t)
  IDL.Interface v Nothing body -> (v, TRec v (objectFromIDL v body))
  otherwise -> error $ "BrownPLT.TypedJS.InitialEnvironment.bindingFromIDL: \
                       \unexpected " ++ show def


makeInitialEnv :: IO (Map String Type)
makeInitialEnv = do
  dataDir <- getDataDir
  let idlPaths = map (dataDir </>) idlFiles
  idls <- mapM IDL.parseIDLFromFile idlPaths
  let idl = removeInheritance (concat idls)
  let toBind (v, t) = (v, Just (t, VPNone))
  return (M.fromList $ (map bindingFromIDL idl) ++ extras)
  
