-- |Tests 'TypedJavaScript.EnvTree'.
--
-- Given a Typed JavaScript program, build its 'EnvTree'.
-- Erase types and transform to JavaScript ANF.
-- Walk the ANF, ensuring that the all 'FuncLit's have a declared type and that
-- local identifiers that are not generated names have a declared type.
--
-- This neglects testing type annotations on fields in objects.
module EnvTree where

import TypedJavaScript.EnvTree (buildEnvTree)
import BrownPLT.JavaScript.Analysis
import TypedJavaScript.TypeErasure (eraseTypesStmts)
import JavaScript.Common()
import TypedJavaScript.Syntax  (Statement)


typedJSAsANF :: [Statement SourcePos]
             -> [Stmt SourcePos]
typeJSAsANF stmts = javaScriptToANF (eraseTypesStmts stmts)



