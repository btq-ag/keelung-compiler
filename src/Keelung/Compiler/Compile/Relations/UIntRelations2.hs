{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}

module Keelung.Compiler.Compile.Relations.UIntRelations2
  ( UIntRelations,
    Lookup (..),
    new,
    lookup,
    assign,
    relate,
    relationBetween,
    -- lookupOneStep,
    inspectChildrenOf,
    isValid,
    toIntMap,
    size,
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe qualified as Maybe
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Keelung (N (N))
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Compile.Relations.Util
import Keelung.Compiler.Constraint (RefU (..))
import Keelung.Interpreter.Arithmetics qualified as Arith
import Keelung.Syntax (HasWidth (widthOf))
import Prelude hiding (lookup)

-- | Relation between a variable and a value or another variable
data Relation n = RootIs Int RefU | Constant n
  deriving (Eq, Show, Generic, NFData)

-- | Relations between UInt variables
data UIntRelations n = UIntRelations
  { -- from children to roots (roots are also in the keys)
    toRoot :: Map RefU (Relation n),
    -- from roots to children, invariant:
    --    1. all "families" are disjoint
    toChildren :: Map RefU (Either n (Map RefU Int))
  }
  deriving (Eq, Generic, NFData)

instance (GaloisField n, Integral n) => Show (UIntRelations n) where
  show relations =
    "UIntRelations\n"
      <> mconcat (map (<> "\n") (concatMap toString (Map.toList backwardLines)))
    where
      showRoot :: RefU -> String
      showRoot root = let rootString = show root in "  " <> rootString <> replicate (8 - length rootString) ' '

      toString :: (RefU, [String]) -> [String]
      toString (root, []) = [showRoot root <> " = []"]
      toString (root, x : xs) = showRoot root <> " = " <> x : map ("           = " <>) xs

      backwardLines :: Map RefU [String]
      backwardLines =
        Map.map
          ( \case
              Left value -> [show (N value)]
              Right xs ->
                map
                  (\(child, rotation) -> show child <> if (rotation `mod` widthOf child) == 0 then "" else " <<< " <> show ((-rotation) `mod` widthOf child))
                  (Map.toList xs)
          )
          (toChildren relations)

-- | Creates a new UIntRelations, O(1)
new :: UIntRelations n
new = UIntRelations mempty mempty

-- | Result of looking up a variable in the UIntRelations
data Lookup n
  = Root
  | Value n
  | -- | The variable is a child of the root rotated LEFt by the given amount
    --   result = root <<< rotation
    ChildOf Int RefU
  deriving (Eq, Show)

-- | Returns the result of looking up a variable in the UIntRelations, O(lg n)
lookup :: (GaloisField n, Integral n) => RefU -> UIntRelations n -> Lookup n
lookup var relations = case Map.lookup var (toRoot relations) of
  Nothing -> Root
  Just (Constant value) -> Value value
  Just (RootIs rotation parent) -> case lookup parent relations of
    Root -> ChildOf rotation parent
    Value value -> Value $ Arith.bitWiseRotateL (widthOf var) rotation value
    ChildOf rotation' grandparent -> ChildOf ((rotation + rotation') `mod` widthOf var) grandparent

-- | Assigns a value to a variable, O(lg n)
assign :: (GaloisField n, Integral n) => RefU -> n -> UIntRelations n -> Except (Error n) (UIntRelations n)
assign ref value relations =
  case lookup ref relations of
    Root -> case Map.lookup ref (toChildren relations) of
      Nothing ->
        return
          relations
            { toRoot = Map.insert ref (Constant value) (toRoot relations),
              toChildren =
                Map.insert ref (Left value) (toChildren relations)
            }
      Just (Left oldvalue) ->
        if oldvalue == value
          then return relations
          else throwError (ConflictingValuesU oldvalue value)
      Just (Right children) -> do
        foldM
          ( \rels (child, rotation) ->
              let value' = Arith.bitWiseRotateL (widthOf ref) rotation value
               in return
                    rels
                      { toRoot = Map.insert child (Constant value') (toRoot rels),
                        toChildren =
                          Map.insert child (Left value') (toChildren rels)
                      }
          )
          ( UIntRelations
              { toRoot = Map.insert ref (Constant value) (toRoot relations),
                toChildren = Map.insert ref (Left value) (toChildren relations)
              }
          )
          (Map.toList children)
    Value oldValue ->
      if oldValue == value
        then return relations -- already assigned
        else throwError (ConflictingValuesU oldValue value)
    ChildOf rotation root ->
      -- ref = root <<< rotation = value
      -- =>
      -- root = value <<< (-rotation)
      assign root (Arith.bitWiseRotateL (widthOf ref) (-rotation) value) relations

-- | Relates two variables, using the more "senior" one as the root, if they have the same seniority, the one with the most children is used, O(lg n)
--   a = b <<< rotation
relate :: (GaloisField n, Integral n) => RefU -> Int -> RefU -> UIntRelations n -> Except (Error n) (UIntRelations n)
relate a rotation b relations =
  case compareSeniority a b of
    LT -> relate' a rotation b relations
    GT -> relate' b (-rotation) a relations
    EQ -> case compare (childrenSizeOf a) (childrenSizeOf b) of
      LT -> relate' a rotation b relations
      GT -> relate' b (-rotation) a relations
      EQ -> relate' a rotation b relations
      where
        childrenSizeOf :: RefU -> Int
        childrenSizeOf ref = case lookup ref relations of
          Root ->
            case Map.lookup ref (toChildren relations) of
              Nothing -> 0
              Just (Left _) -> 0
              Just (Right xs) -> Map.size xs
          Value _ -> 0
          ChildOf _ parent -> childrenSizeOf parent

-- | Relates a child to a parent, child = parent <<< rotation
relate' :: (GaloisField n, Integral n) => RefU -> Int -> RefU -> UIntRelations n -> Except (Error n) (UIntRelations n)
relate' child rotation parent relations =
  case lookup parent relations of
    Root -> case lookup child relations of
      Root -> return $ relateRootToRoot child rotation parent relations
      Value value ->
        -- child = value = parent <<< rotation
        --  =>
        -- parent = value <<< (-rotation)
        assign parent (Arith.bitWiseRotateL (widthOf child) (-rotation) value) relations
      ChildOf rotation' parent' ->
        -- child = parent' <<< rotation', child = parent <<< rotation
        -- =>
        -- parent' <<< rotation' = parent <<< rotation
        -- =>
        -- parent' = parent <<< (rotation - rotation')
        relate parent' (rotation - rotation') parent relations
    Value value ->
      -- child = value = parent <<< rotation
      -- =>
      -- parent = value <<< (-rotation)
      assign child (Arith.bitWiseRotateL (widthOf child) (-rotation) value) relations
    ChildOf rotation' grandparent ->
      -- child = parent <<< rotation, parent = grandparent <<< rotation'
      -- =>
      -- child = grandparent <<< (rotation + rotation')
      relate child (rotation + rotation') grandparent relations

-- | Helper function for `relate'`
relateRootToRoot :: (GaloisField n, Integral n) => RefU -> Int -> RefU -> UIntRelations n -> UIntRelations n
relateRootToRoot child rotation parent relations =
  if child == parent
    then relations -- do nothing if the child is the same as the parent
    else -- before assigning the child to the parent, we need to check if the child has any grandchildren

      let result = case Map.lookup child (toChildren relations) of
            Nothing -> Nothing
            Just (Left _) -> Nothing
            Just (Right xs) -> Just (Map.toList xs)
       in case result of
            Nothing -> addChild child rotation parent relations
            Just grandchildren ->
              removeRootFromBackwardLinks child $
                addChild child rotation parent $
                  foldr
                    ( \(grandchild, rotation') ->
                        addChild grandchild (rotation + rotation') parent
                    )
                    relations
                    grandchildren
  where
    removeRootFromBackwardLinks :: RefU -> UIntRelations n -> UIntRelations n
    removeRootFromBackwardLinks root xs = xs {toChildren = Map.delete root (toChildren xs)}

-- | Helper function for `relate'`
addChild :: RefU -> Int -> RefU -> UIntRelations n -> UIntRelations n
addChild child rotation parent relations =
  let rotation' = rotation `mod` widthOf child
   in relations
        { toRoot = Map.insert child (RootIs rotation' parent) (toRoot relations),
          toChildren = case Map.lookup parent (toChildren relations) of
            Nothing -> Map.insert parent (Right (Map.singleton child rotation')) (toChildren relations)
            Just (Left _) -> toChildren relations
            Just (Right xs) -> Map.insert parent (Right (Map.insert child rotation' xs)) (toChildren relations)
        }

-- | Calculates the relation between two variables `var1` and `var2`
--   Returns `Just rotation` where `rotateLeft rotation var1 = var2` if the two variables are related.
relationBetween :: (GaloisField n, Integral n) => RefU -> RefU -> UIntRelations n -> Maybe Int
relationBetween var1 var2 xs = case (lookup var1 xs, lookup var2 xs) of
  (Root, Root) ->
    if var1 == var2
      then Just 0
      else Nothing -- var1 and var2 are roots, but not the same one
  (Root, ChildOf rotation2 parent2) ->
    if var1 == parent2
      then -- var2 = parent2 <<< rotation2 = var1 <<< rotation2
      -- =>
      -- var1 = var2 <<< (-rotation2)
        Just ((-rotation2) `mod` widthOf var2)
      else Nothing
  (Root, Value _) -> Nothing -- var1 is a root, var2 is a constant value
  (ChildOf rotation1 parent1, Root) ->
    if var2 == parent1
      then -- var1 = parent1 <<< rotation1 = var2 <<< rotation1
        Just (rotation1 `mod` widthOf var1)
      else Nothing
  (Value _, Root) -> Nothing -- var1 is a constant value, var2 is a root
  (ChildOf rotation1 parent1, ChildOf rotation2 parent2) ->
    if parent1 == parent2
      then Just ((rotation1 - rotation2) `mod` widthOf var1)
      else Nothing
  (Value _, ChildOf _ _) -> Nothing -- var1 is a constant value
  (ChildOf _ _, Value _) -> Nothing -- var2 is a constant value
  (Value _, Value _) -> Nothing

-- | Export the internal representation of the relations as a map from variables to their relations
toIntMap :: UIntRelations n -> Map RefU (Either (Int, RefU) n)
toIntMap = fmap go . toRoot
  where
    go :: Relation n -> Either (Int, RefU) n
    go (Constant value) = Right value
    go (RootIs rotation parent) = Left (rotation, parent)

size :: UIntRelations n -> Int
size = Map.size . toRoot

-- -- | Non-recursive version of `lookup`, for inspecting the internal relation between two variables
-- lookupOneStep :: RefU -> UIntRelations n -> Lookup n
-- lookupOneStep var relations = case Map.lookup var (toRoot relations) of
--   Nothing -> Root
--   Just (Constant value) -> Value value
--   Just (RootIs rotation parent) -> ChildOf rotation parent

-- | For inspecting the internal relation between two variables
inspectChildrenOf :: RefU -> UIntRelations n -> Maybe (Either n (Map RefU Int))
inspectChildrenOf ref relations = Map.lookup ref (toChildren relations)

-- | For testing the invariants:
--   1. all "families" are disjoint
--   2. the seniority of the root of a family is greater than equal the seniority of all its children
isValid :: UIntRelations n -> Bool
isValid relations = allFamiliesAreDisjoint relations && rootsAreSenior relations
  where
    allFamiliesAreDisjoint :: UIntRelations n -> Bool
    allFamiliesAreDisjoint = Maybe.isJust . Map.foldlWithKey' go (Just Set.empty) . toChildren
      where
        go :: Maybe (Set RefU) -> RefU -> Either n (Map RefU Int) -> Maybe (Set RefU)
        go Nothing _ _ = Nothing
        go (Just set) root children = case toFamily root children of
          Nothing -> Nothing
          Just members -> if Set.intersection set members == Set.empty then Just (set <> members) else Nothing

        -- return Nothing if the family is not valid, otherwise return the set of variables in the family
        toFamily :: RefU -> Either n (Map RefU Int) -> Maybe (Set RefU)
        toFamily _ (Left _) = Just Set.empty
        toFamily root (Right xs) =
          let children = Map.keysSet xs
           in if root `Set.member` children
                then Nothing
                else Just (Set.insert root children)

    rootsAreSenior :: UIntRelations n -> Bool
    rootsAreSenior = Map.foldlWithKey' go True . toRoot
      where
        go :: Bool -> RefU -> Relation n -> Bool
        go False _ _ = False
        go True ref (RootIs _ root) = compareSeniority root ref /= LT
        go True _ _ = True