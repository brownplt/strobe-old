-- |
-- Maintainer: arjun@cs.brown.edu
--
-- Determine the environment of a JavaScript function.
module TypedJavaScript.Environment
  (
  -- * Environment
    RawEnv
  , globalEnv
  , funcEnv
  , extractReturns
  ) where

import TypedJavaScript.Prelude
import TypedJavaScript.Syntax
import TypedJavaScript.PrettyPrint


isNotFuncExpr :: Expression SourcePos -> Bool
isNotFuncExpr (FuncExpr{}) = False
isNotFuncExpr _            = True

extractReturns :: [Statement SourcePos] -> [Statement SourcePos]
extractReturns statements = 
  everythingBut (++) (mkQ True isNotFuncExpr) query statements where
    
    query :: GenericQ [Statement SourcePos]
    query = mkQ [] collectReturnStmt
    
    collectReturnStmt :: Statement SourcePos -> [Statement SourcePos]
    collectReturnStmt r@(ReturnStmt{}) = [r]
    collectReturnStmt _ = []
    
-- ----------------------------------------------------------------------------
-- Environment

type RawEnv = [(Id SourcePos,
               (Maybe (Type SourcePos)), 
               (Maybe (Expression SourcePos)))] 

globalEnv :: [Statement SourcePos] -> RawEnv
globalEnv globalStatements = 
  everythingBut (++) (mkQ True isNotFuncExpr) query globalStatements where

    query :: GenericQ RawEnv
    query = (mkQ [] collectVarDecl) `extQ` collectForInInit

    collectVarDecl :: VarDecl SourcePos -> RawEnv
    collectVarDecl (VarDecl _ id t)              = [(id,(Just t), Nothing)] 
    collectVarDecl (VarDeclExpr _ id (Just t) e) = [(id,(Just t), (Just e))]
    collectVarDecl (VarDeclExpr _ id Nothing e)  = [(id,Nothing, (Just e))]

    collectForInInit :: ForInInit SourcePos -> RawEnv
    collectForInInit (ForInVar id)  = [] 
     --[(id,error "this type shouldnt be seen", Nothing)]
    -- In vanilla JavaScript, for-in without a var may introduce a global.
    -- We require variables to be declared.  So, without the var, we assume
    -- that the id is already in the environment.  While type-checking, verify
    -- that it is and ensure the declared type matches.
    collectForInInit (ForInNoVar _) = []

-- |The environment of a function, excluding the functions arguments.
-- Signals an error if the expression is not a 'FuncExpr'
funcEnv :: Expression SourcePos -> RawEnv
funcEnv (FuncExpr _ _ _ body) = globalEnv [body]
funcEnv e = error $ "funcEnv: expected a FuncExpr, received " ++ show e
