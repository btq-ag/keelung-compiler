{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# HLINT ignore "Replace case with fromMaybe" #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind
  ( UnionFind,
    relationBetween,
    new,
    parentOf,
    relate,
    bindToValue,
    toMap,
    size,
    bindBoolean,
    relateBoolean,
    HasRefB,
    Lookup (..),
    exportBooleanRelations
  )
where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.List qualified as List
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Keelung.Compiler.Constraint
import Keelung.Compiler.Optimize.MinimizeConstraints.BooleanRelations (BooleanRelations)
import Keelung.Compiler.Optimize.MinimizeConstraints.BooleanRelations qualified as BooleanRelations
import Prelude hiding (lookup)

data UnionFind ref n = UnionFind
  { links :: Map ref (Maybe (n, ref), n),
    sizes :: Map ref Int,
    booleanRelations :: BooleanRelations
  }
  deriving (Eq, Generic, NFData)

instance (Show ref, Show n, Eq n, Num n) => Show (UnionFind ref n) where
  show xs =
    show (booleanRelations xs)
      <> "\n"
      <> "UnionFind {\n"
      ++ "  links = "
      ++ showList' (map showLink (Map.toList $ links xs))
      ++ "\n"
      ++ "  sizes = "
      ++ showList' (map (\(var, n) -> show var <> ": " <> show n) (Map.toList $ sizes xs))
      ++ "\n}"
    where
      showList' ys = "[" <> List.intercalate ", " ys <> "]"

      showLink (var, (Just (slope, root), intercept)) = show var <> " = " <> (if slope == 1 then "" else show slope) <> show root <> (if intercept == 0 then "" else " + " <> show intercept)
      showLink (var, (Nothing, intercept)) = show var <> " = " <> show intercept

new :: Ord ref => UnionFind ref n
new = UnionFind mempty mempty BooleanRelations.new

data Lookup ref n = Root | Constant n | ChildOf n ref n
  deriving (Eq, Show)

-- | Returns 'Nothing' if the variable is already a root.
--   else returns 'Just (slope, root)'  where 'var = slope * root + intercept'
parentOf :: (Ord ref, Num n) => UnionFind ref n -> ref -> Lookup ref n
parentOf xs var = case Map.lookup var (links xs) of
  Nothing -> Root -- var is a root
  Just (Nothing, intercept) -> Constant intercept -- var is a root
  Just (Just (slope, parent), intercept) -> case parentOf xs parent of
    Root ->
      -- parent is a root
      ChildOf slope parent intercept
    Constant intercept' ->
      -- parent is a value
      -- var = slope * parent + intercept
      -- parent = intercept'
      --  =>
      -- var = slope * intercept' + intercept
      Constant (slope * intercept' + intercept)
    ChildOf slope' grandparent intercept' ->
      -- var = slope * parent + intercept
      -- parent = slope' * grandparent + intercept'
      --  =>
      -- var = slope * (slope' * grandparent + intercept') + intercept
      --  =>
      -- var = slope * slope' * grandparent + slope * intercept' + intercept
      ChildOf (slope * slope') grandparent (slope * intercept' + intercept)

-- | Calculates the relation between two variables `var1` and `var2`
--   Returns `Nothing` if the two variables are not related.
--   Returns `Just (slope, intercept)` where `var1 = slope * var2 + intercept` if the two variables are related.
relationBetween :: (Ord ref, GaloisField n) => ref -> ref -> UnionFind ref n -> Maybe (n, n)
relationBetween var1 var2 xs = case (parentOf xs var1, parentOf xs var2) of
  (Root, Root) ->
    if var1 == var2
      then Just (1, 0)
      else Nothing -- var1 and var2 are roots, but not the same one
  (Root, ChildOf slope2 root2 intercept2) ->
    -- var2 = slope2 * root2 + intercept2
    --  =>
    -- root2 = (var2 - intercept2) / slope2
    if var1 == root2
      then -- var1 = root2
      --  =>
      -- var1 = (var2 - intercept2) / slope2
        Just (recip slope2, -intercept2 / slope2)
      else Nothing
  (Root, Constant _) -> Nothing -- var1 is a root, var2 is a value
  (ChildOf slope1 root1 intercept1, Root) ->
    -- var1 = slope1 * root1 + intercept1
    if var2 == root1
      then -- var2 = root1
      --  =>
      -- var1 = slope1 * var2 + intercept1
        Just (slope1, intercept1)
      else Nothing
  (Constant _, Root) -> Nothing -- var1 is a value, var2 is a root
  (ChildOf slope1 root1 intercept1, ChildOf slope2 root2 intercept2) ->
    -- var1 = slope1 * root1 + intercept1
    -- var2 = slope2 * root2 + intercept2
    if root1 == root2
      then -- var2 = slope2 * root2 + intercept2
      --  =>
      -- root2 = (var2 - intercept2) / slope2 = root1
      --  =>
      -- var1 = slope1 * root1 + intercept1
      --  =>
      -- var1 = slope1 * ((var2 - intercept2) / slope2) + intercept1
      --  =>
      -- var1 = slope1 * var2 / slope2 - slope1 * intercept2 / slope2 + intercept1
        Just (slope1 / slope2, -slope1 * intercept2 / slope2 + intercept1)
      else Nothing
  (ChildOf {}, Constant _) -> Nothing -- var2 is a value
  (Constant _, ChildOf {}) -> Nothing -- var1 is a value
  (Constant x, Constant y) ->
    if x == y
      then Just (1, 0)
      else Nothing -- var1 and var2 are values, but not the same one

bindBoolean :: RefB -> Bool -> UnionFind ref n -> UnionFind ref n
bindBoolean ref val xs = xs {booleanRelations = BooleanRelations.bindToValue ref val (booleanRelations xs)}

relateBoolean :: RefB -> (Bool, RefB) -> UnionFind ref n -> UnionFind ref n
relateBoolean refA (same, refB) xs = case BooleanRelations.relate refA (same, refB) (booleanRelations xs) of
  Nothing -> xs
  Just boolRels -> xs {booleanRelations = boolRels}

-- | Bind a variable to a value
bindToValue :: (Ord ref, GaloisField n, HasRefB ref) => ref -> n -> UnionFind ref n -> UnionFind ref n
bindToValue x value xs =
  case extractRefB x of
    Just refB -> bindBoolean refB (value == 1) xs
    Nothing ->
      case parentOf xs x of
        Root ->
          -- x does not have a parent, so it is its own root
          xs
            { links = Map.insert x (Nothing, value) (links xs),
              sizes = Map.insert x 1 (sizes xs)
            }
        Constant _oldValue ->
          -- x is already a root with `_oldValue` as its value
          -- TODO: handle this kind of conflict in the future
          -- FOR NOW: overwrite the value of x with the new value
          xs
            { links = Map.insert x (Nothing, value) (links xs)
            }
        ChildOf slopeP parent interceptP ->
          -- x is a child of `parent` with slope `slopeP` and intercept `interceptP`
          --  x = slopeP * parent + interceptP
          -- now since that x = value, we have
          --  value = slopeP * parent + interceptP
          -- =>
          --  value - interceptP = slopeP * parent
          -- =>
          --  parent = (value - interceptP) / slopeP
          xs
            { links =
                Map.insert parent (Nothing, (value - interceptP) / slopeP) $
                  Map.insert x (Nothing, value) $
                    links xs,
              sizes = Map.insert x 1 (sizes xs)
            }

relate :: (Ord ref, GaloisField n, HasRefB ref) => ref -> (n, ref, n) -> UnionFind ref n -> Maybe (UnionFind ref n)
relate x (0, _, intercept) xs =
  case extractRefB x of
    Just refB -> Just $ bindBoolean refB (intercept == 1) xs
    Nothing -> Just $ bindToValue x intercept xs
relate x (slope, y, intercept) xs =
  case (extractRefB x, extractRefB y) of
    (Just refA, Just refB) -> Just $ relateBoolean refA (slope == 1, refB) xs
    _ -> case compare x y of
      GT -> relate' x (slope, y, intercept) xs -- x = slope * y + intercept
      LT -> relate' y (recip slope, x, -intercept / slope) xs -- y = x / slope - intercept / slope
      EQ -> Nothing

-- | Establish the relation of 'x = slope * y + intercept'
--   Returns Nothing if the relation has already been established
relate' :: (Ord ref, GaloisField n, HasRefB ref) => ref -> (n, ref, n) -> UnionFind ref n -> Maybe (UnionFind ref n)
relate' x (slope, y, intercept) xs =
  case parentOf xs x of
    Constant interceptX ->
      -- x is already a root with `interceptX` as its value
      --  x = slope * y + intercept
      --  x = interceptX
      -- =>
      --  slope * y + intercept = interceptX
      -- =>
      --  y = (interceptX - intercept) / slope
      Just $ bindToValue y (interceptX - intercept / slope) xs
    ChildOf slopeX rootOfX interceptX ->
      -- x is a child of `rootOfX` with slope `slopeX` and intercept `interceptX`
      --  x = slopeX * rootOfX + interceptX
      --  x = slope * y + intercept
      -- =>
      --  slopeX * rootOfX + interceptX = slope * y + intercept
      -- =>
      --  slopeX * rootOfX = slope * y + intercept - interceptX
      -- =>
      --  rootOfX = (slope * y + intercept - interceptX) / slopeX
      relate rootOfX (slope / slopeX, y, intercept - interceptX / slopeX) xs
    Root ->
      -- x does not have a parent, so it is its own root
      case parentOf xs y of
        Constant interceptY ->
          -- y is already a root with `interceptY` as its value
          --  x = slope * y + intercept
          --  y = interceptY
          -- =>
          --  x = slope * interceptY + intercept
          Just $ bindToValue x (slope * interceptY + intercept) xs
        ChildOf slopeY rootOfY interceptY ->
          -- y is a child of `rootOfY` with slope `slopeY` and intercept `interceptY`
          --  y = slopeY * rootOfY + interceptY
          --  x = slope * y + intercept
          -- =>
          --  x = slope * (slopeY * rootOfY + interceptY) + intercept
          -- =>
          --  x = slope * slopeY * rootOfY + slope * interceptY + intercept
          Just $
            xs
              { links = Map.insert x (Just (slope * slopeY, rootOfY), slope * interceptY + intercept) (links xs),
                sizes = Map.insertWith (+) y 1 (sizes xs)
              }
        Root ->
          -- y does not have a parent, so it is its own root
          Just $
            xs
              { links = Map.insert x (Just (slope, y), intercept) (links xs),
                sizes = Map.insertWith (+) y 1 (sizes xs)
              }

toMap :: UnionFind ref n -> Map ref (Maybe (n, ref), n)
toMap = links

size :: UnionFind ref n -> Int
size = Map.size . links



exportBooleanRelations :: UnionFind ref n -> BooleanRelations
exportBooleanRelations = booleanRelations

--------------------------------------------------------------------------------

class HasRefB ref where
  extractRefB :: ref -> Maybe RefB

instance HasRefB RefF where
  extractRefB (RefBtoRefF ref) = Just ref
  extractRefB _ = Nothing

instance HasRefB RefU where
  extractRefB (RefBtoRefU ref) = Just ref
  extractRefB _ = Nothing