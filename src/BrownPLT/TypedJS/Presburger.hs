{-|
 Code to deal w/ Data.Integer.Presburger's lack of open formula support
-}
module BrownPLT.TypedJS.Presburger
  ( OpenFormula(..), OpenTerm(..),
    closeFormula
  ) where

import qualified Data.Set as S
import qualified Data.Map as M
--import qualified Data.Integer.Presburger as Pres
import Data.Integer.Presburger 
import Text.PrettyPrint.HughesPJ

infixl 3 ::/\:
infixl 2 ::\/:
infixr 1 ::=>:
infix 4 ::<:, ::<=:, ::>:, ::>=:, ::=:, ::/=:, ::|

-- First-order formulas for Presburger arithmetic.
data OpenFormula  
  = OpenFormula ::/\: OpenFormula
  | OpenFormula ::\/: OpenFormula
  | OpenFormula ::=>: OpenFormula
  | OpenNot OpenFormula
  | OpenTRUE
  | OpenFALSE
  | OpenTerm ::<:  OpenTerm
  | OpenTerm ::>:  OpenTerm
  | OpenTerm ::<=: OpenTerm
  | OpenTerm ::>=: OpenTerm
  | OpenTerm ::=:  OpenTerm
  | OpenTerm ::/=: OpenTerm
  | Integer ::| OpenTerm

-- Terms ----------------------------------------------------------------------

data OpenTerm = NumberTerm Integer
              | FreeVar    String
              | Plus OpenTerm OpenTerm
              | Minus OpenTerm OpenTerm


-- Useful Functions -----------------------------------------------------------

freeVarsTerm :: OpenTerm -> S.Set String
freeVarsTerm t = case t of
  NumberTerm _ -> S.empty
  FreeVar s -> S.singleton s
  Plus t1 t2 -> S.union (freeVarsTerm t1) (freeVarsTerm t2)
  Minus t1 t2 -> S.union (freeVarsTerm t1) (freeVarsTerm t2)

freeVars :: OpenFormula -> S.Set String
freeVars f = case f of
  f1 ::/\: f2 -> S.union (freeVars f1) (freeVars f2)
  f1 ::\/: f2 -> S.union (freeVars f1) (freeVars f2)
  f1 ::=>: f2 -> S.union (freeVars f1) (freeVars f2)
  OpenNot f1 -> freeVars f1
  OpenTRUE -> S.empty
  OpenFALSE -> S.empty
  t1 ::<: t2 -> S.union (freeVarsTerm t1) (freeVarsTerm t2)
  t1 ::>: t2 -> S.union (freeVarsTerm t1) (freeVarsTerm t2)
  t1 ::<=: t2 -> S.union (freeVarsTerm t1) (freeVarsTerm t2)
  t1 ::>=: t2 -> S.union (freeVarsTerm t1) (freeVarsTerm t2)
  t1 ::=: t2 -> S.union (freeVarsTerm t1) (freeVarsTerm t2)
  t1 ::/=: t2 -> S.union (freeVarsTerm t1) (freeVarsTerm t2)
  i  ::| t -> freeVarsTerm t

substTerm :: M.Map String Term -> OpenTerm -> Term
substTerm m t = case t of
  NumberTerm i -> fromInteger i
  FreeVar s -> case M.lookup s m of
    Nothing -> error "Couldn't subst a term!"
    Just pt -> pt
  Plus t1 t2 -> (substTerm m t1) + (substTerm m t2)
  Minus t1 t2 -> (substTerm m t1) - (substTerm m t2)

subst :: M.Map String Term -> OpenFormula -> Formula
subst m f = case f of
  f1 ::/\: f2 -> (subst m f1) :/\: (subst m f2)
  f1 ::\/: f2 -> (subst m f1) :\/: (subst m f2)
  f1 ::=>: f2 -> (subst m f1) :=>: (subst m f2)
  OpenNot f1 -> Not $ subst m f1
  OpenTRUE -> TRUE
  OpenFALSE -> FALSE
  t1 ::<: t2 -> (substTerm m t1) :<: (substTerm m t2)
  t1 ::>: t2 -> (substTerm m t1) :>: (substTerm m t2)
  t1 ::<=: t2 -> (substTerm m t1) :<=: (substTerm m t2)
  t1 ::>=: t2 -> (substTerm m t1) :>=: (substTerm m t2)
  t1 ::=: t2 -> (substTerm m t1) :=: (substTerm m t2)
  t1 ::/=: t2 -> (substTerm m t1) :/=: (substTerm m t2)
  i  ::| t1 -> i :| (substTerm m t1)

-- Build a map for all open terms to the Forall thing
-- then subst everything at once
_closeFormula :: OpenFormula -> M.Map String Term -> [String] -> Formula
_closeFormula f m [] = subst m f
_closeFormula f m (o:os) = Forall (\x -> _closeFormula f (M.insert o x m) os)

closeFormula :: OpenFormula -> Formula
closeFormula f = _closeFormula f M.empty (S.toList $ freeVars f)

--------------------------------------------------------------------------------

-- Pretty Printing -------------------------------------------------------------

