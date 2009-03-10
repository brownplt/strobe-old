module TypedJavaScript.Prelude
  ( module Data.Generics
  , module Control.Monad
  , module Data.List
  , everythingBut
  ) where


import Data.List
import Data.List
import Data.Generics
import Control.Monad
 
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
