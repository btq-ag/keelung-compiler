{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}

module Keelung.Compiler.Compile.Relations.BooleanRelations2
  ( BooleanRelations,
    Lookup (..),
    new,
    lookup,
    assign,
    relate,
    relationBetween,
    lookupOneStep,
    inspectChildrenOf,
    isValid,
    toIntMap,
    size,
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe qualified as Maybe
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Constraint (RefB (..))
import Prelude hiding (lookup)

-- | Relation between a variable and a value or another variable
data Relation = RootIs Bool RefB | Constant Bool
  deriving (Eq, Show, Generic, NFData)

-- | Relations between Boolean variables
data BooleanRelations = BooleanRelations
  { -- from children to roots (roots are also in the keys)
    toRoot :: Map RefB Relation,
    -- from roots to children, invariant:
    --    1. all "families" are disjoint
    toChildren :: Map RefB (Either Bool (Map RefB Bool))
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
              Right xs ->
                map
                  (\(child, polarity) -> if polarity then show child else "¬ " <> show child)
                  (Map.toList xs)
          )
          (toChildren relations)

-- | Creates a new BooleanRelations, O(1)
new :: BooleanRelations
new = BooleanRelations mempty mempty

-- | Result of looking up a variable in the BooleanRelations
data Lookup = Root | Value Bool | ChildOf Bool RefB
  deriving (Eq, Show)

-- | Returns the result of looking up a variable in the BooleanRelations, O(lg n)
lookup :: RefB -> BooleanRelations -> Lookup
lookup var relations = case Map.lookup var (toRoot relations) of
  Nothing -> Root
  Just (Constant value) -> Value value
  Just (RootIs polarity parent) -> case lookup parent relations of
    Root -> ChildOf polarity parent
    Value value -> Value (polarity == value)
    ChildOf polarity' grandparent -> ChildOf (polarity == polarity') grandparent

-- | Assigns a value to a variable, O(lg n)
assign :: RefB -> Bool -> BooleanRelations -> Except (Error n) BooleanRelations
assign ref value relations = case lookup ref relations of
  Root ->
    return
      relations
        { toRoot = Map.insert ref (Constant value) (toRoot relations),
          toChildren = Map.insert ref (Left value) (toChildren relations)
        }
  Value oldValue ->
    if oldValue == value
      then return relations -- already assigned
      else throwError (ConflictingValuesB oldValue value)
  ChildOf polarity parent -> assign parent (polarity == value) relations

-- | Relates two variables, using the more "senior" one as the root, if they have the same seniority, the one with the most children is used, O(lg n)
relate :: RefB -> Bool -> RefB -> BooleanRelations -> Except (Error n) BooleanRelations
relate a polarity b relations = case compareSeniority a b of
  LT -> relate' a polarity b relations
  GT -> relate' b polarity a relations
  EQ -> case compare (childrenSizeOf a) (childrenSizeOf b) of
    LT -> relate' a polarity b relations
    GT -> relate' b polarity a relations
    EQ -> relate' a polarity b relations
    where
      childrenSizeOf :: RefB -> Int
      childrenSizeOf ref = case lookup ref relations of
        Root ->
          case Map.lookup ref (toChildren relations) of
            Nothing -> 0
            Just (Left _) -> 0
            Just (Right xs) -> Map.size xs
        Value _ -> 0
        ChildOf _ parent -> childrenSizeOf parent

-- | Relates a child to a parent
relate' :: RefB -> Bool -> RefB -> BooleanRelations -> Except (Error n) BooleanRelations
relate' child polarity parent relations =
  case lookup parent relations of
    Root -> case lookup child relations of
      Root -> return $ relateRootToRoot child polarity parent relations
      Value value -> assign parent (polarity == value) relations
      ChildOf polarity' parent' -> relate' parent' (polarity == polarity') parent relations
    Value value -> assign child (polarity == value) relations
    ChildOf polarity' grandparent ->
      relate' child (polarity == polarity') grandparent relations

-- | Helper function for `relate'`
relateRootToRoot :: RefB -> Bool -> RefB -> BooleanRelations -> BooleanRelations
relateRootToRoot child polarity parent relations =
  -- before assigning the child to the parent, we need to check if the child has any grandchildren
  let result = case Map.lookup child (toChildren relations) of
        Nothing -> Nothing
        Just (Left _) -> Nothing
        Just (Right xs) -> Just (Map.toList xs)
   in case result of
        Nothing -> addChild child polarity parent relations
        Just grandchildren ->
          removeRootFromBackwardLinks child $ addChild child polarity parent $ foldr (\(grandchild, polarity') -> addChild grandchild (polarity == polarity') parent) relations grandchildren
  where
    removeRootFromBackwardLinks :: RefB -> BooleanRelations -> BooleanRelations
    removeRootFromBackwardLinks root xs = xs {toChildren = Map.delete root (toChildren xs)}

-- | Helper function for `relate'`
addChild :: RefB -> Bool -> RefB -> BooleanRelations -> BooleanRelations
addChild child polarity parent relations =
  relations
    { toRoot = Map.insert child (RootIs polarity parent) (toRoot relations),
      toChildren = case Map.lookup parent (toChildren relations) of
        Nothing -> Map.insert parent (Right (Map.singleton child polarity)) (toChildren relations)
        Just (Left _) -> toChildren relations
        Just (Right xs) -> Map.insert parent (Right (Map.insert child polarity xs)) (toChildren relations)
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

-- | Export the internal representation of the relations as a map from variables to their relations
toIntMap :: BooleanRelations -> Map RefB (Either (Bool, RefB) Bool)
toIntMap = fmap go . toRoot
  where
    go :: Relation -> Either (Bool, RefB) Bool
    go (Constant value) = Right value
    go (RootIs polarity parent) = Left (polarity, parent)

size :: BooleanRelations -> Int
size = Map.size . toRoot

-- | Non-recursive version of `lookup`, for inspecting the internal relation between two variables
lookupOneStep :: RefB -> BooleanRelations -> Lookup
lookupOneStep var relations = case Map.lookup var (toRoot relations) of
  Nothing -> Root
  Just (Constant value) -> Value value
  Just (RootIs polarity parent) -> ChildOf polarity parent

-- | For inspecting the internal relation between two variables
inspectChildrenOf :: RefB -> BooleanRelations -> Maybe (Either Bool (Map RefB Bool))
inspectChildrenOf ref relations = Map.lookup ref (toChildren relations)

-- | For testing the invariants:
--   1. all "families" are disjoint
isValid :: BooleanRelations -> Bool
isValid = Maybe.isJust . Map.foldlWithKey' go (Just Set.empty) . toChildren
  where
    go :: Maybe (Set RefB) -> RefB -> Either Bool (Map RefB Bool) -> Maybe (Set RefB)
    go Nothing _ _ = Nothing
    go (Just set) root children = case toFamily root children of
      Nothing -> Nothing
      Just members -> if Set.intersection set members == Set.empty then Just (set <> members) else Nothing

    -- return Nothing if the family is not valid, otherwise return the set of variables in the family
    toFamily :: RefB -> Either Bool (Map RefB Bool) -> Maybe (Set RefB)
    toFamily _ (Left _) = Just Set.empty
    toFamily root (Right xs) =
      let children = Map.keysSet xs
       in if root `Set.member` children
            then Nothing
            else Just (Set.insert root children)

--------------------------------------------------------------------------------

class Seniority a where
  compareSeniority :: a -> a -> Ordering

instance Seniority RefB where
  compareSeniority (RefBX _) (RefBX _) = EQ
  compareSeniority (RefBX _) _ = LT
  compareSeniority _ (RefBX _) = GT
  compareSeniority _ _ = EQ