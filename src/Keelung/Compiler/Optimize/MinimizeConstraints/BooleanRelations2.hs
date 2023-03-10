{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}

module Keelung.Compiler.Optimize.MinimizeConstraints.BooleanRelations2
  ( BooleanRelations,
    Relation (..),
    Lookup (..),
    new,
    lookup,
    assign,
    relate,
    relationBetween,
    lookupOneStep,
    inspectChildrenOf,
  )
where

import Control.DeepSeq (NFData)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Keelung.Compiler.Constraint (RefB (..))
import Prelude hiding (lookup)

-- | Relation between a variable and a value or another variable
data Relation = ParentIs Bool RefB | Constant Bool
  deriving (Eq, Show, Generic, NFData)

-- | Relations between Boolean variables
data BooleanRelations = BooleanRelations
  { -- from children to roots (roots are also in the keys)
    forwardLinks :: Map RefB Relation,
    -- from roots to children
    backwardLinks :: Map RefB (Either Bool (Map RefB Bool))
  }
  deriving (Eq, Generic, NFData)

instance Show BooleanRelations where
  show relations =
    "BooleanRelations\n"
      <> mconcat (map (<> "\n") (concatMap toString (Map.toList backwardLines)))
      <> " backward links: "
      <> show (backwardLinks relations)
      <> "}"
    where
      showRoot :: RefB -> String
      showRoot root = let rootString = show root in "  " <> rootString <> replicate (8 - length rootString) ' '

      toString :: (RefB, [String]) -> [String]
      toString (root, []) = [showRoot root <> " = []"]
      toString (root, x : xs) = showRoot root <> " = " <> x : map ("           = " <>) xs

      backwardLines :: Map RefB [String]
      backwardLines =
        Map.map
          ( \case
              Left value -> [show value]
              Right toChildren ->
                map
                  (\(child, polarity) -> if polarity then show child else "¬ " <> show child)
                  (Map.toList toChildren)
          )
          (backwardLinks relations)

-- | Creates a new BooleanRelations, O(1)
new :: BooleanRelations
new = BooleanRelations mempty mempty

-- | Result of looking up a variable in the BooleanRelations
data Lookup = Root | Value Bool | ChildOf Bool RefB
  deriving (Eq, Show)

-- | Returns the result of looking up a variable in the BooleanRelations, O(lg n)
lookup :: RefB -> BooleanRelations -> Lookup
lookup var relations = case Map.lookup var (forwardLinks relations) of
  Nothing -> Root
  Just (Constant value) -> Value value
  Just (ParentIs polarity parent) -> case lookup parent relations of
    Root -> ChildOf polarity parent
    Value value -> Value (polarity == value)
    ChildOf polarity' grandparent -> ChildOf (polarity == polarity') grandparent

-- | Assigns a value to a variable, O(lg n)
assign :: RefB -> Bool -> BooleanRelations -> BooleanRelations
assign ref value relations = case lookup ref relations of
  Root ->
    relations
      { forwardLinks = Map.insert ref (Constant value) (forwardLinks relations),
        backwardLinks = Map.insert ref (Left value) (backwardLinks relations)
      }
  Value _ -> relations -- already assigned
  ChildOf polarity parent -> assign parent (polarity == value) relations

-- | Relates two variables, using the smaller one as the root, O(lg n)
relate :: RefB -> Bool -> RefB -> BooleanRelations -> BooleanRelations
relate a polarity b relations
  | a > b = relate' a polarity b relations
  | a < b = relate' b polarity a relations
  | otherwise = relations

-- | Relates a child to a parent
relate' :: RefB -> Bool -> RefB -> BooleanRelations -> BooleanRelations
relate' child polarity parent relations = case lookup parent relations of
  Root ->
    -- before assigning the child to the parent, we need to check if the child has any grandchildren
    let result = case Map.lookup child (backwardLinks relations) of
          Nothing -> Nothing
          Just (Left _) -> Nothing
          Just (Right xs) -> Just (Map.toList xs)
     in case result of
          Nothing -> addChild child polarity parent relations
          Just grandchildren ->
            removeRootFromBackwardLinks child $ addChild child polarity parent $ foldr (\(grandchild, polarity') -> addChild grandchild polarity' parent) relations grandchildren
  Value value -> assign child (polarity == value) relations
  -- relate the child to the grandparent instead
  ChildOf polarity' grandparent -> relate' child (polarity == polarity') grandparent relations
  where
    removeRootFromBackwardLinks :: RefB -> BooleanRelations -> BooleanRelations
    removeRootFromBackwardLinks root xs = xs {backwardLinks = Map.delete root (backwardLinks xs)}

-- | Helper function for `relate'`
addChild :: RefB -> Bool -> RefB -> BooleanRelations -> BooleanRelations
addChild child polarity parent relations =
  relations
    { forwardLinks = Map.insert child (ParentIs polarity parent) (forwardLinks relations),
      backwardLinks = case Map.lookup parent (backwardLinks relations) of
        Nothing -> Map.insert parent (Right (Map.singleton child polarity)) (backwardLinks relations)
        Just (Left _) -> backwardLinks relations
        Just (Right xs) -> Map.insert parent (Right (Map.insert child polarity xs)) (backwardLinks relations)
    }

-- | Calculates the relation between two variables `var1` and `var2`
--   Returns `Just relation` where `var1 = polarity == var2` if the two variables are related.
relationBetween :: RefB -> RefB -> BooleanRelations -> Maybe Bool
relationBetween var1 var2 xs = case (lookup var1 xs, lookup var2 xs) of
  (Root, Root) ->
    if var1 == var2
      then Just True
      else Nothing -- var1 and var2 are roots, but not the same one
  (Root, ChildOf polarity2 parent2) ->
    if var1 == parent2
      then Just polarity2
      else Nothing
  (Root, Value _) -> Nothing -- var1 is a root, var2 is a constant value
  (ChildOf polarity1 parent1, Root) ->
    if var2 == parent1
      then Just polarity1
      else Nothing
  (Value _, Root) -> Nothing -- var1 is a constant value, var2 is a root
  (ChildOf polarity1 parent1, ChildOf polarity2 parent2) ->
    if parent1 == parent2
      then Just (polarity1 == polarity2)
      else Nothing
  (Value _, ChildOf _ _) -> Nothing -- var1 is a constant value
  (ChildOf _ _, Value _) -> Nothing -- var2 is a constant value
  (Value value1, Value value2) -> Just (value1 == value2)

-- -- | Bind a variable to a value
-- bindToValue :: RefB -> Bool -> BooleanRelations -> BooleanRelations
-- bindToValue x value xs =
--   case lookup xs x of
--     Root ->
--       -- x does not have a parent, so it is its own root
--       rememberPinnedBitTest x $
--         xs
--           { links = Map.insert x (Right value) (links xs),
--             sizes = Map.insert x 1 (sizes xs)
--           }
--     Constant _oldValue ->
--       -- x is already a root with `_oldValue` as its value
--       -- TODO: handle this kind of conflict in the future
--       -- FOR NOW: overwrite the value of x with the new value
--       rememberPinnedBitTest x $
--         xs
--           { links = Map.insert x (Right value) (links xs)
--           }
--     ChildOf relation parent ->
--       rememberPinnedBitTest x $
--         xs
--           { links =
--               Map.insert parent (Right (value == relation)) $
--                 Map.insert x (Right value) $
--                   links xs,
--             sizes = Map.insert x 1 (sizes xs)
--           }

-- relate :: RefB -> (Bool, RefB) -> BooleanRelations -> Maybe BooleanRelations
-- relate x (relation, y) xs
--   | x > y = relate' x (relation, y) xs
--   | x < y = relate' y (relation, x) xs
--   | otherwise = Nothing

-- -- | Establish the relation of 'x = (relation == y)'
-- --   Returns Nothing if the relation has already been established
-- relate' :: RefB -> (Bool, RefB) -> BooleanRelations -> Maybe BooleanRelations
-- relate' x (relation, y) xs = case lookup xs x of
--   Constant constantX ->
--     Just $ bindToValue y (relation == constantX) xs
--   ChildOf relationX rootOfX ->
--     relate rootOfX (relation == relationX, y) xs
--   Root ->
--     -- x does not have a parent, so it is its own root
--     case lookup xs y of
--       Constant constantY ->
--         Just $ bindToValue x (relation == constantY) xs
--       ChildOf relationY rootOfY ->
--         Just $
--           rememberPinnedBitTest x $
--             xs
--               { links = Map.insert x (Left (relation == relationY, rootOfY)) (links xs),
--                 sizes = Map.insertWith (+) y 1 (sizes xs)
--               }
--       Root ->
--         -- y does not have a parent, so it is its own root
--         Just $
--           rememberPinnedBitTest x $
--             xs
--               { links = Map.insert x (Left (relation, y)) (links xs),
--                 sizes = Map.insertWith (+) y 1 (sizes xs)
--               }

-- size :: BooleanRelations -> Int
-- size = Map.size . links

-- exportPinnedBitTests :: BooleanRelations -> Set RefB
-- exportPinnedBitTests = Set.map (\(w, ref, i) -> RefUBit w ref i) . pinnedBitTests

-- toIntMap :: BooleanRelations -> Map RefB (Either (Bool, RefB) Bool)
-- toIntMap = links

-- | Non-recursive version of `lookup`, for inspecting the internal relation between two variables
lookupOneStep :: RefB -> BooleanRelations -> Lookup
lookupOneStep var relations = case Map.lookup var (forwardLinks relations) of
  Nothing -> Root
  Just (Constant value) -> Value value
  Just (ParentIs polarity parent) -> ChildOf polarity parent

-- | For inspecting the internal relation between two variables
inspectChildrenOf :: RefB -> BooleanRelations -> Maybe (Either Bool (Map RefB Bool))
inspectChildrenOf ref relations = Map.lookup ref (backwardLinks relations)