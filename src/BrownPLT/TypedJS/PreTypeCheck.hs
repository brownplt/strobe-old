-- |Check that the programs is syntactically well-formed.  Perform this check
-- before checking that the program is typable.
--
-- If @preTypeCheck@ succeeds, the following are true for the program:
--
-- * The program does not have any free variables, given an initial environment.
--
-- * All statements in the program are reachable.
--
-- * All variables are defined before they are used.
module BrownPLT.TypedJS.PreTypeCheck
  ( preTypeCheck
  , preTypeCheckTopLevel
  , allPathsReturn
  ) where

import BrownPLT.TypedJS.FreeVars
import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.LocalVars
import BrownPLT.TypedJS.RuntimeAnnotations (runtimeAnnotations)
import BrownPLT.TypedJS.TypeDefinitions
import BrownPLT.TypedJS.TypeTheory
import BrownPLT.TypedJS.PrettyPrint
import BrownPLT.TypedJS.Syntax
import qualified Data.Map as M
import qualified Data.Set as S
import BrownPLT.JavaScript.Analysis (toANF, Stmt)
import BrownPLT.JavaScript.Analysis.DefineBeforeUse
import BrownPLT.TypedJS.TypeErasure
import BrownPLT.TypedJS.ReachableStatements
import qualified BrownPLT.JavaScript.Analysis.AllPathsReturn as AllPathsReturn


type ANF = ([(String, SourcePos)], [Stmt SourcePos])


allPathsReturn :: Statement SourcePos
               -> Bool
allPathsReturn s = case AllPathsReturn.allPathsReturn s' of
  -- This should have been caught earlier.
  Left err -> error ("PreTypeCheck.hs: " ++ err)
  Right r -> r
  where s' = case eraseTypes [s] of
               [s''] -> s''
               otherwise -> 
                 error "PreTypeCheck.hs: shape mismatch from eraseTypes"


checkClosed globals body = case freeVars globals body of
  [] -> return ()
  freeVars -> fail $ "free variables: " ++ show freeVars

checkReachability :: ANF -> Either String ()
checkReachability anf = case unreachableStatements anf of
  [] -> return ()
  ss -> fail $ "Unreachable statements at " ++ show ss


preTypeCheckTopLevel :: (MonadError String m)
                     => [String] -- ^globals
                     -> [TopLevel SourcePos] -- ^source
                     -> m ()
preTypeCheckTopLevel globals program = do
  -- TODO: checkClosed globals body
  case toANF (map eraseTypesTopLevel program) of
    Right anf -> case checkReachability anf of
      Right _ -> case defineBeforeUse (S.fromList ("this":globals)) anf of
        Right () -> return ()
        Left err -> fail (show err)
      Left err -> fail err
    Left err -> fail err


preTypeCheck :: [String] -- ^globals
             -> [Statement SourcePos] -- ^source
             -> Either String [Statement SourcePos]
preTypeCheck globals body = do
  checkClosed globals body
  anf <- toANF (eraseTypes body)
  checkReachability anf
  case defineBeforeUse (S.fromList ("this":globals)) anf of
    Right () -> Right body
    Left errs -> Left (show errs)
