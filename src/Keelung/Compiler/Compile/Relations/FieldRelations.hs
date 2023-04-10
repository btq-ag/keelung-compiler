{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# HLINT ignore "Replace case with fromMaybe" #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Compiler.Compile.Relations.FieldRelations
  ( FieldRelations,
    relationBetween,
    new,
    parentOf,
    relateRefF,
    bindField,
    bindUInt,
    bindBoolean,
    assertEqualUInt,
    relateBoolean,
    toMap,
    size,
    Lookup (..),
    exportBooleanRelations,
    exportUIntRelations,
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import Data.List qualified as List
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Compile.Relations.BooleanRelations (BooleanRelations)
import Keelung.Compiler.Compile.Relations.BooleanRelations qualified as BooleanRelations
import Keelung.Compiler.Compile.Relations.UIntRelations (UIntRelations)
import Keelung.Compiler.Compile.Relations.UIntRelations qualified as UIntRelations
import Keelung.Compiler.Constraint
import Prelude hiding (lookup)

data FieldRelations n = FieldRelations
  { links :: Map RefF (Maybe (n, RefF), n),
    sizes :: Map RefF Int,
    booleanRelations :: BooleanRelations,
    uintRelations :: UIntRelations n
  }
  deriving (Eq, Generic, NFData)

instance (GaloisField n, Integral n) => Show (FieldRelations n) where
  show xs =
    show (booleanRelations xs)
      <> "\n"
      <> show (uintRelations xs)
      <> "\n"
      <> "FieldRelations {\n"
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

new :: FieldRelations n
new = FieldRelations mempty mempty BooleanRelations.new UIntRelations.new

data Lookup n = Root | Constant n | ChildOf n RefF n
  deriving (Eq, Show)

-- | Returns 'Nothing' if the variable is already a root.
--   else returns 'Just (slope, root)'  where 'var = slope * root + intercept'
parentOf :: Integral n => FieldRelations n -> RefF -> Lookup n
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
relationBetween :: (GaloisField n, Integral n) => RefF -> RefF -> FieldRelations n -> Maybe (n, n)
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

bindBoolean :: RefB -> Bool -> FieldRelations n -> Except (Error n) (FieldRelations n)
bindBoolean ref val xs = do
  result <- BooleanRelations.assign ref val (booleanRelations xs)
  return $ xs {booleanRelations = result}

-- | Bind a variable to a value
bindUInt :: (GaloisField n, Integral n) => RefU -> n -> FieldRelations n -> Except (Error n) (FieldRelations n)
bindUInt ref val xs = do
  result <- UIntRelations.bindToValue ref val (uintRelations xs)
  return $ xs {uintRelations = result}

assertEqualUInt :: (GaloisField n, Integral n) => RefU -> RefU -> FieldRelations n -> Except (Error n) (FieldRelations n)
assertEqualUInt refA refB xs = do
  result <- UIntRelations.assertEqual refA refB (uintRelations xs)
  case result of
    Nothing -> return xs
    Just uintRels -> return $ xs {uintRelations = uintRels}

relateBoolean :: RefB -> (Bool, RefB) -> FieldRelations n -> Except (Error n) (FieldRelations n)
relateBoolean refA (same, refB) xs = do
  result <- BooleanRelations.relate refA same refB (booleanRelations xs)
  return $ xs {booleanRelations = result}

-- | Bind a variable to a value
bindField :: (GaloisField n, Integral n) => RefF -> n -> FieldRelations n -> Except (Error n) (FieldRelations n)
bindField x value xs =
  case x of
    RefBtoRefF refB -> bindBoolean refB (value == 1) xs
    RefUVal refU -> bindUInt refU value xs -- NOTE: unreachable
    _ ->
      case parentOf xs x of
        Root ->
          -- x does not have a parent, so it is its own root
          return $
            xs
              { links = Map.insert x (Nothing, value) (links xs),
                sizes = Map.insert x 1 (sizes xs)
              }
        Constant oldValue ->
          if oldValue == value
            then
              return $
                xs
                  { links = Map.insert x (Nothing, value) (links xs)
                  }
            else throwError $ ConflictingValuesF oldValue value
        ChildOf slopeP parent interceptP ->
          -- x is a child of `parent` with slope `slopeP` and intercept `interceptP`
          --  x = slopeP * parent + interceptP
          -- now since that x = value, we have
          --  value = slopeP * parent + interceptP
          -- =>
          --  value - interceptP = slopeP * parent
          -- =>
          --  parent = (value - interceptP) / slopeP
          return $
            xs
              { links =
                  Map.insert parent (Nothing, (value - interceptP) / slopeP) $
                    Map.insert x (Nothing, value) $
                      links xs,
                sizes = Map.insert x 1 (sizes xs)
              }

relateRefF :: (GaloisField n, Integral n) => RefF -> (n, RefF, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefF x (slope, y, intercept) xs =
  case (x, y, slope, intercept) of
    (RefBtoRefF refB, _, 0, value) -> Just <$> bindBoolean refB (value == 1) xs
    (RefUVal refU, _, 0, value) -> Just <$> bindUInt refU value xs
    (_, _, 0, value) -> Just <$> bindField x value xs
    (RefBtoRefF refA, RefBtoRefF refB, 1, 0) -> Just <$> relateBoolean refA (True, refB) xs
    (RefUVal refA, RefUVal refB, 1, 0) -> Just <$> assertEqualUInt refA refB xs
    (RefBtoRefF refA, RefBtoRefF refB, -1, 1) -> Just <$> relateBoolean refA (False, refB) xs
    _ -> case compare x y of
      GT -> relateRefF' x (slope, y, intercept) xs -- x = slope * y + intercept
      LT -> relateRefF' y (recip slope, x, -intercept / slope) xs -- y = x / slope - intercept / slope
      EQ -> return Nothing

-- | Establish the relation of 'x = slope * y + intercept'
--   Returns Nothing if the relation has already been established
relateRefF' :: (GaloisField n, Integral n) => RefF -> (n, RefF, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefF' x (slope, y, intercept) xs =
  case parentOf xs x of
    Constant interceptX ->
      -- x is already a root with `interceptX` as its value
      --  x = slope * y + intercept
      --  x = interceptX
      -- =>
      --  slope * y + intercept = interceptX
      -- =>
      --  y = (interceptX - intercept) / slope
      Just <$> bindField y (interceptX - intercept / slope) xs
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
      relateRefF rootOfX (slope / slopeX, y, intercept - interceptX / slopeX) xs
    Root ->
      -- x does not have a parent, so it is its own root
      case parentOf xs y of
        Constant interceptY ->
          -- y is already a root with `interceptY` as its value
          --  x = slope * y + intercept
          --  y = interceptY
          -- =>
          --  x = slope * interceptY + intercept
          Just <$> bindField x (slope * interceptY + intercept) xs
        ChildOf slopeY rootOfY interceptY ->
          -- y is a child of `rootOfY` with slope `slopeY` and intercept `interceptY`
          --  y = slopeY * rootOfY + interceptY
          --  x = slope * y + intercept
          -- =>
          --  x = slope * (slopeY * rootOfY + interceptY) + intercept
          -- =>
          --  x = slope * slopeY * rootOfY + slope * interceptY + intercept
          return $
            Just $
              xs
                { links = Map.insert x (Just (slope * slopeY, rootOfY), slope * interceptY + intercept) (links xs),
                  sizes = Map.insertWith (+) y 1 (sizes xs)
                }
        Root ->
          -- y does not have a parent, so it is its own root
          return $
            Just $
              xs
                { links = Map.insert x (Just (slope, y), intercept) (links xs),
                  sizes = Map.insertWith (+) y 1 (sizes xs)
                }

toMap :: FieldRelations n -> Map RefF (Maybe (n, RefF), n)
toMap = links

size :: FieldRelations n -> Int
size = Map.size . links

exportBooleanRelations :: FieldRelations n -> BooleanRelations
exportBooleanRelations = booleanRelations

exportUIntRelations :: FieldRelations n -> UIntRelations n
exportUIntRelations = uintRelations