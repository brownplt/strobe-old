-- |Removes @VarDeclStmt@s from Typed JavaScript expressions.
module BrownPLT.TypedJS.EraseVarDecl
  ( removeVarDeclsEverywhere
  )  where

import BrownPLT.TypedJS.Prelude
import BrownPLT.TypedJS.Syntax


instance Typeable SourcePos where
  typeOf _  = 
    mkTyConApp (mkTyCon "Text.ParserCombinators.Parsec.Pos.SourcePos") []

    
-- Complete guesswork.  It seems to work.
sourcePosDatatype = mkDataType "SourcePos" [sourcePosConstr1]
sourcePosConstr1 = mkConstr sourcePosDatatype "SourcePos" [] Prefix


-- |We make 'SourcePos' an instance of 'Typeable' so that we can use it with
-- generics.
--
-- This definition is incomplete.
instance Data SourcePos where
  -- We treat source locations as opaque.  After all, we don't have access to
  -- the constructor.
  gfoldl k z pos = z pos
  toConstr _ = sourcePosConstr1
  gunfold   = error "gunfold is not defined for SourcePos"
  dataTypeOf = error "dataTypeOf is not defined for SourcePos"


isEmptyStmt (EmptyStmt _) = True
isEmptyStmt _ = False


removeEmpty :: Statement SourcePos
            -> Statement SourcePos
removeEmpty (BlockStmt p []) = EmptyStmt p
removeEmpty (BlockStmt p ss) = case filter (not . isEmptyStmt) ss of
                                 [] -> EmptyStmt p
                                 ss' -> BlockStmt p ss'
removeEmpty s = s


removeEmptyEverywhere :: Statement SourcePos
                      -> Statement SourcePos
removeEmptyEverywhere stmt = everywhere (mkT removeEmpty) stmt


toBinds :: [Statement a] -> [Binding a]
toBinds ss = concatMap unStmt ss
  where unStmt (VarDeclStmt _ decls) = map unDecl decls
        unStmt _ = error "EraseVarDecl.hs : toBinds expected VarDeclStmt"
        unDecl (VarDecl a (Id _ x) ty) = 
            (x, VarRef a (Id a "undefined"), Just ty)
        unDecl (VarDeclExpr a (Id _ x) maybeTy e) =
            (x, e, maybeTy)
        unDecl (UnpackDecl a (Id _ x) tVars e) =
            (x, UnpackExpr a tVars e, Nothing)


isLetRecBinding  :: Statement a -> Bool
isLetRecBinding (VarDeclStmt _ decls) = all f decls
  where f (VarDeclExpr _ _ _ (FuncExpr{})) = True
        f _ = False
isLetRecBinding _ = False


addLetRec :: [Statement SourcePos]
          -> [Statement SourcePos]
addLetRec ss = case partition isLetRecBinding ss of
  ([], []) -> [] -- @ss@ was empty
  ([], s:ss') -> s:(addLetRec ss')
  (binds, body) -> [ExprStmt noPos (LetRecExpr noPos (toBinds binds) body')]
    where body' = case addLetRec body of
                    [] -> EmptyStmt noPos -- signs of awful coding style
                    [s] -> s -- sir, you are an ML hacker
                    ss' -> BlockStmt noPos ss' -- no comment ...


isLetBinding (VarDeclStmt _ _) = True
isLetBinding _ = False


addLet :: [Statement SourcePos]
          -> [Statement SourcePos]
addLet ss = case partition isLetBinding ss of
  ([], []) -> []
  ([], s:ss') -> s:(addLet ss')
  (binds, body) -> [ExprStmt noPos (LetExpr noPos (toBinds binds) body')]
    where body' = case addLet body of
                    [] -> EmptyStmt noPos
                    [s] -> s
                    ss' -> BlockStmt noPos ss'

removeVarDecls :: Statement SourcePos
               -> Statement SourcePos
removeVarDecls stmt = case stmt of
  BlockStmt p ss -> case addLet (addLetRec ss) of
    [] -> EmptyStmt p -- shouldn't happen, but whatever
    [s] -> s
    ss' -> BlockStmt p ss'
  -- really odd case
  VarDeclStmt p ds -> ExprStmt p $ case isLetRecBinding stmt of
    True -> LetRecExpr p (toBinds [stmt]) (EmptyStmt p)
    False -> LetExpr p (toBinds [stmt]) (EmptyStmt p)
  otherwise -> stmt

removeVarDeclsEverywhere :: Statement SourcePos
                         -> Statement SourcePos
removeVarDeclsEverywhere stmt = 
  everywhere (mkT removeVarDecls) (removeEmptyEverywhere stmt)
