module BrownPLT.TypedJS.TypeDefinitions
  ( Type(..)
  , VP(..)
  , LatentPred(..)
  , TypeConstraint (..)
  ) where

import TypedJavaScript.Syntax

-- |Our type system uses local control flow to refine types (i.e. type unions).
-- Furthermore, an assignment to a variable of a type union will usually refine
-- its type as well.
--
-- However, not
data LocalType
  = LocalType Type -- declared type
              Type -- current type, based on local control flow
  | GlobalType Type -- declared type
               
