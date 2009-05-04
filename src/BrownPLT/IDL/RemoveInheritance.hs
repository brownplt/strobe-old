-- |Removes inheritance from interface definitions, expanding all interfaces
-- to contain all their methods and attributes.
module BrownPLT.IDL.RemoveInheritance
  ( removeInheritance
  ) where

import Data.Map (Map)
import Data.Set (Set)
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import BrownPLT.IDL.Syntax


unique :: Ord a => [a] -> Maybe a
unique xs = isUnique
  where uniqueM set [] = Right set
        uniqueM set (x:xs) = case S.member x set of
          False -> uniqueM (S.insert x set) xs
          True -> Left x
        isUnique = case uniqueM S.empty xs of
          Left x -> Just x
          Right _ -> Nothing


-- |Returns a map from names to interfaces.
interfaceMap :: [Definition] -> Map Id Definition
interfaceMap defs = foldl add M.empty defs 
  where err name _ = error $ "BrownPLT.IDL.RemoveInheritance.interfaceMap: " ++
                             name ++ " occurs multiple times"
        add im def = case def of
          Interface name _ _ -> M.insertWith (err name) name def im
          otherwise -> im


-- |Ensures all names are unique
catMembers :: [Definition] -> [Definition] -> Either String [Definition]
catMembers fs1 fs2 = case unique (map definitionName (fs1 ++ fs2)) of
  Just x -> Left x
  Nothing -> Right (fs1 ++ fs2)


-- |Returns all the members of an interface, including inherited members.
-- Returns an expanded definitions map.
uninherit :: Map Id Definition
          -> Id
          -> ([Definition], Map Id Definition)
uninherit im name = case M.lookup name im of
  Just (Interface _ Nothing fs) -> (fs, im)
  Just (Interface _ (Just parent) fs) -> (fs'', im'')
    where (fs', im') = uninherit im parent
          fs'' = case catMembers fs fs' of
                   Right members -> members
                   Left s -> 
                     error $ "BrownPLT.IDL.RemoveInheritance.uninherit: \
                             \overlapping names with parent: " ++ name ++
                             " and its parent " ++ parent ++ " define " ++ s
          im'' = M.insert name (Interface name Nothing fs'') im'
  Just def -> error $ "BrownPLT.IDL.RemoveInheritance.uninherit: unexpected in \
                      \interface map: " ++ show def
  Nothing -> error $ "BrownPLT.IDL.RemoveInheritance.uninherit: nonexistant \
                     \interface: " ++ name


uninheritAll :: Map Id Definition
             -> [Id]
             -> [Definition]
uninheritAll im [] = []
uninheritAll im (name:names) = def:(uninheritAll im' names)
  where (members, im') = uninherit im name
        def = Interface name Nothing members

isInterface (Interface _ _ _) = True
isInterface _ = False



-- |Expands interfaces to include their inherited fields.
removeInheritance :: [Definition] -> [Definition]
removeInheritance defs = others ++ interfaces'
  where (interfaces, others) = partition isInterface defs
        im = interfaceMap interfaces
        interfaces' = uninheritAll im (M.keys im)
