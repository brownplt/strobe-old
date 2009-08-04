-- |Returns the locally declared variables and type variables in a function.
-- Type variables are associated with their type annotation, or their initial
-- expression, if the variable does not have a type annotation.
module BrownPLT.TypedJS.LocalVars
  ( localVars
  , topLevelVars
  , LocalDecl(..)
  ) where

import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.Syntax
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad.Error


data LocalDecl
  = DeclType String Type
  | DeclExpr String (Expression SourcePos)
  | DeclField String String (Expression SourcePos)
  | DeclConstr String Type
  | DeclUnpack String [String] (Expression SourcePos)


data S =  S {
  sVarList :: [LocalDecl],
  sTVars :: Set String,
  sBoundVars :: Set String
}


type Locals a = ErrorT String (State S) a


bind :: String
     -> Type
     -> Locals ()
bind x t = do
  s <- get
  case S.member x (sBoundVars s) of
    False -> put (s { sVarList = (DeclType x t):(sVarList s),
                      sBoundVars = S.insert x (sBoundVars s) })
    True -> fail $ printf "%s is declared multiple times" x


bindExpr :: String
         -> Expression SourcePos
         -> Locals ()
bindExpr x e = do
  s <- get
  case S.member x (sBoundVars s) of
    False -> put (s { sVarList = (DeclExpr x e):(sVarList s),
                      sBoundVars = S.insert x (sBoundVars s) })
    True -> fail $ printf "%s is declared multiple times" x


bindField :: String
          -> String
          -> Expression SourcePos
          -> Locals ()
bindField brand field e = do
  s <- get
  put $ s { sVarList = (DeclField brand field e):(sVarList s) }


bindConstr :: String
           -> Type
           -> Locals ()
bindConstr brand ty = do
  s <- get
  put $ s { sVarList = (DeclConstr brand ty):(sVarList s) }


bindUnpack :: String
           -> [String]
           -> Expression SourcePos
           -> Locals ()
bindUnpack x tVars e = do
  s <- get
  put s { sVarList = (DeclUnpack x tVars e):(sVarList s) }


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
varDecl (UnpackDecl _ x tVars e) = bindUnpack (unId x) tVars e
 
 
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

topLevel :: TopLevel SourcePos -> Locals ()
topLevel tl = case tl of
  TopLevelStmt s -> stmt s
  ExternalFieldStmt _ (Id _ brand) (Id _ field) e -> bindField brand field e
  ConstructorStmt _ brand _ ty _ -> bindConstr brand ty
  ImportStmt _ name _ ty -> bind (unId name) ty


topLevelVars :: MonadError String m
             => [String] -- ^imports
             -> [TopLevel SourcePos]
             -> m ([LocalDecl], [String])
topLevelVars binds tl = 
  case runState (runErrorT $ mapM_ topLevel tl)
                (S [] S.empty (S.fromList binds)) of
    (Left err, _) -> fail err
    (Right (), S vars tvars _) -> return (reverse vars, S.toList tvars)
             


localVars :: [String] -- ^ function arguments
          -> Statement SourcePos
          -> Either String ([LocalDecl], [String])
localVars binds s =
  case runState (runErrorT (stmt s)) (S [] S.empty (S.fromList binds)) of
    (Left err, _) -> Left err
    (Right (), S vars tvars _) -> Right (reverse vars, S.toList tvars)
