-- |Common exports.  Defines a monad instance for 'Either String'.
module BrownPLT.TypedJS.Prelude
  ( module Data.Generics
  , module Control.Monad
  , module Data.List
  , module Data.Maybe
  , module Data.Tree
  , SourcePos
  , initialPos
  , sourceName
  , sourceLine
  , sourceColumn
  , (!)
  , Map
  , Set
  , Foldable
  , Traversable
  , printf
  -- common functions
  , noPos
  , everythingBut
  , catastrophe
  , isLeft, isRight, procEither
  , Node
  ) where

import Data.Tree
import Data.List
import Data.Generics
import Data.Maybe
import Control.Monad
import Text.ParserCombinators.Parsec.Pos
import Data.Map (Map,(!))
import Data.Set (Set)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Text.PrettyPrint.HughesPJ
import Text.Printf
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive (Node, Graph)

instance Monad (Either String) where
  return v = Right v
  fail s = Left s
  (Left s) >>= _ = Left s
  (Right v) >>= f = f v


-- |'initialPos ""'
noPos :: SourcePos
noPos = initialPos ""


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




catastrophe :: Monad m
            => SourcePos
            -> String
            -> m a
catastrophe loc msg =
  fail $ printf "CATASTROPHIC FAILURE: %s (at %s)" msg (show loc)

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

procEither :: (a -> b) -> Either a a -> Either b b
procEither f (Left t) = Left (f t)
procEither f (Right t) = Right (f t)
