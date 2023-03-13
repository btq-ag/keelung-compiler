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

-- | Relates two variables, using the more "senior" one as the root, O(lg n)
relate :: RefB -> Bool -> RefB -> BooleanRelations -> BooleanRelations
relate a polarity b relations = case compareSeniority a b of
  LT -> relate' a polarity b relations
  GT -> relate' b polarity a relations
  EQ -> case compare (childrenSizeOf a relations) (childrenSizeOf b relations) of
    LT -> relate' a polarity b relations
    GT -> relate' b polarity a relations
    EQ -> relate' a polarity b relations

-- | Relates a child to a parent
relate' :: RefB -> Bool -> RefB -> BooleanRelations -> BooleanRelations
relate' child polarity parent relations =
  case lookup parent relations of
    Root -> case lookup child relations of
      Root -> relateRootToRoot child polarity parent relations
      Value value -> assign parent (polarity == value) relations
      ChildOf polarity' parent' -> relate' parent' (polarity == polarity') parent relations
    Value value -> assign child (polarity == value) relations
    ChildOf polarity' grandparent ->
      relate' child (polarity == polarity') grandparent relations

-- | Helper function for `relate'`
relateRootToRoot :: RefB -> Bool -> RefB -> BooleanRelations -> BooleanRelations
relateRootToRoot child polarity parent relations =
  -- before assigning the child to the parent, we need to check if the child has any grandchildren
  let result = case Map.lookup child (backwardLinks relations) of
        Nothing -> Nothing
        Just (Left _) -> Nothing
        Just (Right xs) -> Just (Map.toList xs)
   in case result of
        Nothing -> addChild child polarity parent relations
        Just grandchildren ->
          removeRootFromBackwardLinks child $ addChild child polarity parent $ foldr (\(grandchild, polarity') -> addChild grandchild (polarity == polarity') parent) relations grandchildren
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

-- | Non-recursive version of `lookup`, for inspecting the internal relation between two variables
lookupOneStep :: RefB -> BooleanRelations -> Lookup
lookupOneStep var relations = case Map.lookup var (forwardLinks relations) of
  Nothing -> Root
  Just (Constant value) -> Value value
  Just (ParentIs polarity parent) -> ChildOf polarity parent

-- | For inspecting the internal relation between two variables
inspectChildrenOf :: RefB -> BooleanRelations -> Maybe (Either Bool (Map RefB Bool))
inspectChildrenOf ref relations = Map.lookup ref (backwardLinks relations)

childrenSizeOf :: RefB -> BooleanRelations -> Int
childrenSizeOf ref relations = case lookup ref relations of
  Root ->
    case Map.lookup ref (backwardLinks relations) of
      Nothing -> 0
      Just (Left _) -> 0
      Just (Right xs) -> Map.size xs
  Value _ -> 0
  ChildOf _ parent -> childrenSizeOf parent relations

--------------------------------------------------------------------------------

class Seniority a where
  compareSeniority :: a -> a -> Ordering

instance Seniority RefB where
  compareSeniority (RefB _) (RefB _) = EQ
  compareSeniority (RefB _) _ = LT
  compareSeniority _ (RefB _) = GT
  compareSeniority _ _ = EQ