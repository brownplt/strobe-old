-- |Returns the locally declared variables and type variables in a function.
-- Type variables are associated with their type annotation, or their initial
-- expression, if the variable does not have a type annotation.
module BrownPLT.TypedJS.LocalVars
  ( localVars
  ) where

import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.Syntax
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad.Error

data S =  S {
  sVars :: Map String (Either (Expression SourcePos) Type),
  sTVars :: Set String,
  sArgs :: Set String
}


type Locals a = ErrorT String (State S) a


bind :: String
     -> Type
     -> Locals ()
bind x t = do
  s <- get
  case S.member x (sArgs s) of
    False -> case M.lookup x (sVars s) of
      Nothing -> put (s { sVars = M.insert x (Right t) (sVars s) })
      Just _ -> fail $ printf "%s is declared multiple times" x
    True -> fail $ printf "%s is declared as a local variable and an argument" x


bindExpr :: String
         -> Expression SourcePos
         -> Locals ()
bindExpr x e = do
  s <- get
  case S.member x (sArgs s) of
    False -> case M.lookup x (sVars s) of
      Nothing -> put (s { sVars = M.insert x (Left e) (sVars s) })
      Just _ -> fail $ printf "%s is declared multiple times" x
    True -> fail $ printf "%s is declared as a local variable and an argument" x


bindTVar :: String -> Locals ()
bindTVar x = do
 s <- get
 case S.member x (sTVars s) of
   False -> put (s { sTVars = S.insert x (sTVars s) })
   True -> fail $ printf "the type variable %s is declared multiple times" x


varDecl :: VarDecl SourcePos -> Locals () 
varDecl (VarDecl _ x t) = bind (unId x) t
varDecl (VarDeclExpr _ x (Just t) _) = bind (unId x) t
varDecl (VarDeclExpr _ x Nothing e) = bindExpr (unId x) e
varDecl (UnpackDecl _ x tVar t _) = do
  bind (unId x) t
  bindTVar tVar
 
 
caseClause :: CaseClause SourcePos -> Locals ()
caseClause cc = case cc of
  CaseClause _ e ss -> mapM_ stmt ss
  CaseDefault _ ss -> mapM_ stmt ss
 

catchClause :: CatchClause SourcePos -> Locals ()
catchClause (CatchClause _ id s) = stmt s


forInit :: ForInit SourcePos -> Locals ()
forInit (VarInit decls) = mapM_ varDecl decls
forInit _ = return ()
 
 
stmt :: Statement SourcePos -> Locals ()
stmt s = case s of
  BlockStmt _ ss -> mapM_ stmt ss
  EmptyStmt _ -> return ()
  ExprStmt _ _ -> return ()
  IfStmt _ _ s1 s2 -> stmt s1 >> stmt s2
  IfSingleStmt _ _ s -> stmt s
  SwitchStmt _ _ cases -> mapM_ caseClause cases
  WhileStmt _ _ s -> stmt s
  DoWhileStmt _ s _ -> stmt s
  BreakStmt _ _ -> return ()
  ContinueStmt _ _ -> return ()
  LabelledStmt _ _ s -> stmt s
  ForInStmt _ _ _ s -> stmt s
  ForStmt _ fi _ _ s -> forInit fi >> stmt s
  TryStmt _ s catches ms -> do
    stmt s
    mapM_ catchClause catches
    case ms of
      Nothing -> return ()
      Just f -> stmt f
  ThrowStmt _ _ -> return ()
  ReturnStmt _ _ -> return ()
  VarDeclStmt _ decls -> mapM_ varDecl decls


localVars :: [String] -- ^ function arguments
          -> Statement SourcePos
          -> Either String
                    ([(String, Either (Expression SourcePos) Type)],
                     [String])
localVars binds s =
  case runState (runErrorT (stmt s)) (S M.empty S.empty (S.fromList binds)) of
    (Left err, _) -> Left err
    (Right (), S vars tvars _) -> Right (M.toList vars, S.toList tvars)
