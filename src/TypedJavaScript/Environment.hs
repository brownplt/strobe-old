-- |
-- Maintainer: arjun@cs.brown.edu
--
-- Determine the environment of a JavaScript function.
module TypedJavaScript.Environment
  (
  -- * Generics for 'SourcePos'
  -- $sourcepos
  -- * Environment
    RawEnv
  , globalEnv
  , funcEnv
  , extractReturns
  ) where

import Data.Generics
import Data.List (foldl')

import Text.ParserCombinators.Parsec(SourcePos)
import TypedJavaScript.Syntax

-- |Similar to 'everything'.  'everythingBut' descends into 'term' only if
-- the generic predicate is 'True'.  If the predicate is 'False',
-- the query is still applied to 'term'.
everythingBut :: (r -> r -> r)  -- ^combines results
              -> GenericQ Bool  -- ^generic predicate that determines whether
                                -- to descend into a value
              -> GenericQ r     -- ^generic query
              -> GenericQ r
everythingBut combine canDescend query term = case canDescend term of
  False -> query term -- does not descend
  True  -> foldl' combine (query term)
                  (gmapQ (everythingBut combine canDescend query) term)

-- -----------------------------------------------------------------------------
-- Generics for SourcePos

-- $sourcepos
-- This module defines 'Typeable' and 'Data' instances for 'SourcePos'.  These
-- definitions are complete guesswork.  However, this is the third project in
-- which definitions have worked just fine.

instance Typeable SourcePos where
  typeOf _  = 
    mkTyConApp (mkTyCon "Text.ParserCombinators.Parsec.Pos.SourcePos") []
    
sourcePosDatatype = mkDataType "SourcePos" [sourcePosConstr1]
sourcePosConstr1 = mkConstr sourcePosDatatype "SourcePos" [] Prefix

instance Data SourcePos where
  -- We treat source locations as opaque values.
  gfoldl k z pos = z pos
  toConstr _ = sourcePosConstr1
  gunfold   = error "gunfold is not defined for SourcePos"
  dataTypeOf = error "dataTypeOf is not defined for SourcePos"

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

type RawEnv = [(Id SourcePos,Either (Expression SourcePos) (Type SourcePos))] 

globalEnv :: [Statement SourcePos] -> RawEnv
globalEnv globalStatements = 
  everythingBut (++) (mkQ True isNotFuncExpr) query globalStatements where

    query :: GenericQ RawEnv
    query = (mkQ [] collectVarDecl) `extQ` collectForInInit

    collectVarDecl :: VarDecl SourcePos -> RawEnv
    collectVarDecl (VarDecl _ id t)              = [(id,Right t)] 
    collectVarDecl (VarDeclExpr _ id (Just t) _) = [(id,Right t)] -- TODO: this is not correct, as the types may not match.
    collectVarDecl (VarDeclExpr _ id Nothing e)  = [(id,Left e)]

    collectForInInit :: ForInInit SourcePos -> RawEnv
    collectForInInit (ForInVar id t)  = [(id,Right t)]
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
