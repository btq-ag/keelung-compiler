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
    relateRef,
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
  { links :: Map Ref (Maybe (n, Ref), n),
    sizes :: Map Ref Int,
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

data Lookup n = Root | Constant n | ChildOf n Ref n
  deriving (Eq, Show)

-- | Returns 'Nothing' if the variable is already a root.
--   else returns 'Just (slope, root)'  where 'var = slope * root + intercept'
parentOf :: Integral n => FieldRelations n -> Ref -> Lookup n
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
relationBetween :: (GaloisField n, Integral n) => Ref -> Ref -> FieldRelations n -> Maybe (n, n)
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
bindField :: (GaloisField n, Integral n) => Ref -> n -> FieldRelations n -> Except (Error n) (FieldRelations n)
bindField x value xs =
  case x of
    B refB -> bindBoolean refB (value == 1) xs
    U refU -> bindUInt refU value xs -- NOTE: unreachable
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

relateRef :: (GaloisField n, Integral n) => Ref -> (n, Ref, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRef x (slope, y, intercept) xs = do
  case (x, y, slope, intercept) of
    (B refB, _, 0, value) -> Just <$> bindBoolean refB (value == 1) xs
    (U refU, _, 0, value) -> Just <$> bindUInt refU value xs
    (_, _, 0, value) -> Just <$> bindField x value xs
    (B refA, B refB, 1, 0) -> Just <$> relateBoolean refA (True, refB) xs
    (U refA, U refB, 1, 0) -> Just <$> assertEqualUInt refA refB xs
    (B refA, B refB, -1, 1) -> Just <$> relateBoolean refA (False, refB) xs
    (F _, F _, _, _) -> relateTwoRefs x (slope, y, intercept) xs
    (F refA, B refB, _, _) -> relateRefFwithRefB refA (slope, refB, intercept) xs
    (F refA, U refB, _, _) -> relateRefFwithRefUX refA (slope, refB, intercept) xs
    (B refA, F refB, _, _) -> relateRefFwithRefB refB (recip slope, refA, -intercept / slope) xs
    (B refA, B refB, _, _) -> relateRefBwithRefB refA (slope, refB, intercept) xs
    (B refA, U refB, _, _) -> relateRefBwithRefUX refA (slope, refB, intercept) xs
    (U refA, F refB, _, _) -> relateRefFwithRefUX refB (recip slope, refA, -intercept / slope) xs
    (U refA, B refB, _, _) -> relateRefBwithRefUX refB (recip slope, refA, -intercept / slope) xs
    (U refA, U refB, _, _) -> relateRefUwithRefUX refA (slope, refB, intercept) xs

relateRefFwithRefB :: (GaloisField n, Integral n) => RefT -> (n, RefB, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefFwithRefB refA (slope, refB, intercept) xs = case (parentOf xs (F refA), BooleanRelations.lookup refB (booleanRelations xs)) of
  (Root, BooleanRelations.Root) -> relateTwoRefs (F refA) (slope, B refB, intercept) xs
  (Root, BooleanRelations.Value True) ->
    -- refA = slope * 1 + intercept
    Just <$> bindField (F refA) (slope + intercept) xs
  (Root, BooleanRelations.Value False) ->
    -- refA = slope * 0 + intercept
    Just <$> bindField (F refA) intercept xs
  (Root, BooleanRelations.ChildOf True rootB) ->
    -- refA = slope * rootB + intercept
    relateTwoRefs (F refA) (slope, B rootB, intercept) xs
  (Root, BooleanRelations.ChildOf False rootB) ->
    -- refA = slope * (1 - rootB) + intercept
    --      = - slope * rootB + slope + intercept
    relateTwoRefs (F refA) (-slope, B rootB, slope + intercept) xs
  (Constant valueA, BooleanRelations.Root) ->
    -- valueA = slope * refB + intercept
    -- =>
    -- refB = (valueA - intercept) / slope
    Just <$> bindField (B refB) ((valueA - intercept) / slope) xs
  (Constant valueA, BooleanRelations.Value True) ->
    -- valueA = slope * 1 + intercept
    if valueA == slope + intercept
      then return Nothing
      else throwError $ ConflictingValuesF valueA (slope + intercept)
  (Constant valueA, BooleanRelations.Value False) ->
    -- valueA = slope * 0 + intercept
    if valueA == intercept
      then return Nothing
      else throwError $ ConflictingValuesF valueA intercept
  (Constant valueA, BooleanRelations.ChildOf True rootB) ->
    -- valueA = slope * rootB + intercept
    -- =>
    -- rootB = (valueA - intercept) / slope
    Just <$> bindField (B rootB) ((valueA - intercept) / slope) xs
  (Constant valueA, BooleanRelations.ChildOf False rootB) ->
    -- valueA = slope * (1 - rootB) + intercept
    -- =>
    -- rootB = (valueA - slope - intercept) / (-slope)
    Just <$> bindField (B rootB) ((valueA - slope - intercept) / (-slope)) xs
  (ChildOf slopeA rootA interceptA, BooleanRelations.Root) ->
    -- slopeA * refA + interceptA = slope * refB + intercept
    -- =>
    -- slopeA * refA = slope * refB + intercept - interceptA
    -- =>
    -- refA = (slope * refB + intercept - interceptA) / slopeA
    relateTwoRefs rootA (slope / slopeA, B refB, (intercept - interceptA) / slopeA) xs
  (ChildOf slopeA rootA interceptA, BooleanRelations.Value True) ->
    -- slopeA * refA + interceptA = slope * 1 + intercept
    -- =>
    -- slopeA * refA = slope + intercept - interceptA
    -- =>
    -- refA = (slope + intercept - interceptA) / slopeA
    Just <$> bindField rootA ((slope + intercept - interceptA) / slopeA) xs
  (ChildOf slopeA rootA interceptA, BooleanRelations.Value False) ->
    -- slopeA * refA + interceptA = slope * 0 + intercept
    -- =>
    -- slopeA * refA = intercept - interceptA
    -- =>
    -- refA = (intercept - interceptA) / slopeA
    Just <$> bindField rootA ((intercept - interceptA) / slopeA) xs
  (ChildOf slopeA rootA interceptA, BooleanRelations.ChildOf True rootB) ->
    -- slopeA * refA + interceptA = slope * rootB + intercept
    -- =>
    -- slopeA * refA = slope * rootB + intercept - interceptA
    -- =>
    -- refA = (slope * rootB + intercept - interceptA) / slopeA
    relateTwoRefs rootA (slope / slopeA, B rootB, (intercept - interceptA) / slopeA) xs
  (ChildOf slopeA rootA interceptA, BooleanRelations.ChildOf False rootB) ->
    -- slopeA * refA + interceptA = slope * (1 - rootB) + intercept
    -- =>
    -- slopeA * refA = slope * (1 - rootB) + intercept - interceptA
    -- =>
    -- slopeA * refA = - slope * rootB + slope + intercept - interceptA
    -- =>
    -- refA = (- slope * rootB + slope + intercept - interceptA) / slopeA
    relateTwoRefs rootA (-slope / slopeA, B rootB, (slope + intercept - interceptA) / slopeA) xs

relateRefFwithRefUX :: (GaloisField n, Integral n) => RefT -> (n, RefU, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefFwithRefUX refA (slope, refB, intercept) xs = case (parentOf xs (F refA), UIntRelations.lookup (uintRelations xs) refB) of
  (Root, UIntRelations.Root) -> relateTwoRefs (F refA) (slope, U refB, intercept) xs
  (Root, UIntRelations.Value value) ->
    -- x = slope * value + intercept
    Just <$> bindField (F refA) (slope * value + intercept) xs
  (Root, UIntRelations.RotateOf 0 root) ->
    -- x = slope * root + intercept
    relateTwoRefs (F refA) (slope, U root, intercept) xs
  (Root, UIntRelations.RotateOf _ _) -> error "[ panic ]: Don't know how to relate a field element to a rotated UInt"
  (Constant value, UIntRelations.Root) ->
    -- value = slope * root + intercept
    -- =>
    -- root = (value - intercept) / slope
    Just <$> bindField (U refB) ((value - intercept) / slope) xs
  (Constant valueA, UIntRelations.Value valueB) ->
    if valueA == slope * valueB + intercept
      then return Nothing
      else throwError $ ConflictingValuesF valueA (slope * valueB + intercept)
  (Constant valueA, UIntRelations.RotateOf 0 root) ->
    -- value = slope * root + intercept
    -- =>
    -- root = (value - intercept) / slope
    Just <$> bindField (U root) ((valueA - intercept) / slope) xs
  (Constant _, UIntRelations.RotateOf _ _) -> error "[ panic ]: Don't know how to relate a field element to a rotated UInt"
  (ChildOf slopeA rootA interceptA, UIntRelations.Root) ->
    -- slopeA * rootA + interceptA = slope * root + intercept
    -- =>
    -- slopeA * rootA = slope * root + intercept - interceptA
    -- =>
    -- rootA = (slope * root + intercept - interceptA) / slopeA
    relateTwoRefs rootA (slope / slopeA, U refB, (intercept - interceptA) / slopeA) xs
  (ChildOf slopeA rootA interceptA, UIntRelations.Value valueB) ->
    -- slopeA * rootA + interceptA = slope * valueB + intercept
    -- =>
    -- slopeA * rootA = slope * valueB + intercept - interceptA
    -- =>
    -- rootA = (slope * valueB + intercept - interceptA) / slopeA
    Just <$> bindField rootA ((slope * valueB + intercept - interceptA) / slopeA) xs
  (ChildOf slopeA rootA interceptA, UIntRelations.RotateOf 0 rootB) ->
    -- slopeA * rootA + interceptA = slope * rootB + intercept
    -- =>
    -- slopeA * rootA = slope * rootB + intercept - interceptA
    -- =>
    -- rootA = (slope * rootB + intercept - interceptA) / slopeA
    relateTwoRefs rootA (slope / slopeA, U rootB, (intercept - interceptA) / slopeA) xs
  (ChildOf {}, UIntRelations.RotateOf _ _) -> error "[ panic ]: Don't know how to relate a field element to a rotated UInt"

relateRefUwithRefUX :: (GaloisField n, Integral n) => RefU -> (n, RefU, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefUwithRefUX refA (slope, refB, intercept) xs = case (UIntRelations.lookup (uintRelations xs) refA, UIntRelations.lookup (uintRelations xs) refB) of
  (UIntRelations.Root, UIntRelations.Root) -> relateTwoRefs (U refA) (slope, U refB, intercept) xs
  (UIntRelations.Root, UIntRelations.Value value) ->
    -- x = slope * value + intercept
    Just <$> bindField (U refA) (slope * value + intercept) xs
  (UIntRelations.Root, UIntRelations.RotateOf 0 root) ->
    -- x = slope * root + intercept
    relateTwoRefs (U refA) (slope, U root, intercept) xs
  (UIntRelations.Root, UIntRelations.RotateOf _ _) -> error "[ panic ]: Don't know how to relate a field element to a rotated UInt"
  (UIntRelations.Value value, UIntRelations.Root) ->
    -- value = slope * rootB + intercept
    -- =>
    -- value - intercept = slope * rootB
    Just <$> bindField (U refB) ((value - intercept) / slope) xs
  (UIntRelations.Value valueA, UIntRelations.Value valueB) ->
    -- valueA = slope * valueB + intercept
    if valueA == slope * valueB + intercept
      then return Nothing
      else throwError $ ConflictingValuesF valueA (slope * valueB + intercept)
  (UIntRelations.Value value, UIntRelations.RotateOf 0 root) ->
    -- value = slope * root + intercept
    Just <$> bindField (U root) ((value - intercept) / slope) xs
  (UIntRelations.Value _, UIntRelations.RotateOf _ _) -> error "[ panic ]: Don't know how to relate a field element to a rotated UInt"
  (UIntRelations.RotateOf 0 root, UIntRelations.Root) ->
    -- rootA = slope * rootB + intercept
    relateTwoRefs (U root) (slope, U refB, intercept) xs
  (UIntRelations.RotateOf 0 rootA, UIntRelations.Value value) ->
    -- rootA = slope * value + intercept
    Just <$> bindField (U rootA) (slope * value + intercept) xs
  (UIntRelations.RotateOf 0 rootA, UIntRelations.RotateOf 0 rootB) ->
    -- rootA = slope * rootB + intercept
    relateTwoRefs (U rootA) (slope, U rootB, intercept) xs
  (UIntRelations.RotateOf 0 _, UIntRelations.RotateOf _ _) -> error "[ panic ]: Don't know how to relate a field element to a rotated UInt"
  (UIntRelations.RotateOf _ _, _) -> error "[ panic ]: Don't know how to relate a field element to a rotated UInt"

relateRefBwithRefUX :: (GaloisField n, Integral n) => RefB -> (n, RefU, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefBwithRefUX refA (slope, refB, intercept) xs = case (BooleanRelations.lookup refA (booleanRelations xs), UIntRelations.lookup (uintRelations xs) refB) of
  (BooleanRelations.Root, UIntRelations.Root) -> relateTwoRefs (B refA) (slope, U refB, intercept) xs
  (BooleanRelations.Root, UIntRelations.Value value) ->
    -- x = slope * value + intercept
    Just <$> bindField (B refA) (slope * value + intercept) xs
  (BooleanRelations.Root, UIntRelations.RotateOf 0 root) ->
    -- x = slope * root + intercept
    relateTwoRefs (B refA) (slope, U root, intercept) xs
  (BooleanRelations.Root, UIntRelations.RotateOf _ _) -> error "[ panic ]: Don't know how to relate a Boolean to a rotated uint"
  (BooleanRelations.Value True, UIntRelations.Root) ->
    -- 1 = slope * rootB + intercept
    -- =>
    -- rootB = (1 - intercept) / slope
    Just <$> bindUInt refB ((1 - intercept) / slope) xs
  (BooleanRelations.Value True, UIntRelations.Value value) ->
    -- 1 = slope * value + intercept
    -- =>
    -- value = (1 - intercept) / slope
    if 1 == slope * value + intercept then return Nothing else throwError $ ConflictingValuesF 1 (slope * value + intercept)
  (BooleanRelations.Value True, UIntRelations.RotateOf 0 root) ->
    -- 1 = slope * root + intercept
    -- =>
    -- root = (1 - intercept) / slope
    Just <$> bindField (U root) ((1 - intercept) / slope) xs
  (BooleanRelations.Value True, UIntRelations.RotateOf _ _) -> error "[ panic ]: Don't know how to relate a Boolean to a rotated uint"
  (BooleanRelations.Value False, UIntRelations.Root) ->
    -- 0 = slope * rootB + intercept
    -- =>
    -- rootB = - intercept / slope
    Just <$> bindUInt refB (-intercept / slope) xs
  (BooleanRelations.Value False, UIntRelations.Value value) ->
    -- 0 = slope * value + intercept
    -- =>
    -- value = - intercept / slope
    if 0 == slope * value + intercept then return Nothing else throwError $ ConflictingValuesF 0 (slope * value + intercept)
  (BooleanRelations.Value False, UIntRelations.RotateOf 0 root) ->
    -- 0 = slope * root + intercept
    -- =>
    -- root = - intercept / slope
    Just <$> bindField (U root) (-intercept / slope) xs
  (BooleanRelations.Value False, UIntRelations.RotateOf _ _) -> error "[ panic ]: Don't know how to relate a Boolean to a rotated uint"
  (BooleanRelations.ChildOf True root, UIntRelations.Root) ->
    -- root = slope * rootB + intercept
    relateTwoRefs (B root) (slope, U refB, intercept) xs
  (BooleanRelations.ChildOf True root, UIntRelations.Value value) ->
    -- root = slope * value + intercept
    Just <$> bindField (B root) (slope * value + intercept) xs
  (BooleanRelations.ChildOf True rootA, UIntRelations.RotateOf 0 rootB) ->
    -- rootA = slope * rootB + intercept
    relateTwoRefs (B rootA) (slope, U rootB, intercept) xs
  (BooleanRelations.ChildOf True _, UIntRelations.RotateOf _ _) -> error "[ panic ]: Don't know how to relate a Boolean to a rotated uint"
  (BooleanRelations.ChildOf False rootA, UIntRelations.Root) ->
    -- rootA = 1 - x && x = slope * rootB + intercept
    -- =>
    -- rootA = 1 - (slope * rootB + intercept)
    -- =>
    -- rootA = 1 - slope * rootB - intercept
    relateTwoRefs (B rootA) (-slope, U refB, 1 - intercept) xs
  (BooleanRelations.ChildOf False rootA, UIntRelations.Value value) ->
    -- rootA = 1 - x && x = slope * value + intercept
    -- =>
    -- rootA = 1 - (slope * value + intercept)
    -- =>
    -- rootA = 1 - slope * value - intercept
    Just <$> bindField (B rootA) (1 - slope * value - intercept) xs
  (BooleanRelations.ChildOf False rootA, UIntRelations.RotateOf 0 rootB) ->
    -- rootA = 1 - x && x = slope * rootB + intercept
    -- =>
    -- rootA = 1 - (slope * rootB + intercept)
    -- =>
    -- rootA = 1 - slope * rootB - intercept
    relateTwoRefs (B rootA) (-slope, U rootB, 1 - intercept) xs
  (BooleanRelations.ChildOf False _, UIntRelations.RotateOf _ _) -> error "[ panic ]: Don't know how to relate a Boolean to a rotated uint"

relateRefBwithRefB :: (GaloisField n, Integral n) => RefB -> (n, RefB, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefBwithRefB refA (slope, refB, intercept) xs =
  case (BooleanRelations.lookup refA (booleanRelations xs), BooleanRelations.lookup refB (booleanRelations xs)) of
    (BooleanRelations.Root, BooleanRelations.Root) -> relateTwoRefs (B refA) (slope, B refB, intercept) xs
    (BooleanRelations.Root, BooleanRelations.Value True) ->
      -- x = slope * 1 + intercept
      Just <$> bindField (B refA) (slope + intercept) xs
    (BooleanRelations.Root, BooleanRelations.Value False) ->
      -- x = slope * 0 + intercept
      Just <$> bindField (B refA) intercept xs
    (BooleanRelations.Root, BooleanRelations.ChildOf True root) ->
      -- x = slope * root + intercept
      relateTwoRefs (B refA) (slope, B root, intercept) xs
    (BooleanRelations.Root, BooleanRelations.ChildOf False root) ->
      -- x = slope * (1 - root) + intercept
      relateTwoRefs (B refA) (-slope, B root, slope + intercept) xs
    (BooleanRelations.Value True, BooleanRelations.Root) ->
      -- 1 = slope * root + intercept
      -- =>
      -- root = (intercept - 1) / slope
      Just <$> bindField (B refB) ((intercept - 1) / slope) xs
    (BooleanRelations.Value True, BooleanRelations.Value True) ->
      if 1 == slope + intercept then return Nothing else throwError $ ConflictingValuesF 1 (slope + intercept)
    (BooleanRelations.Value True, BooleanRelations.Value False) ->
      if 1 == intercept then return Nothing else throwError $ ConflictingValuesF 1 intercept
    (BooleanRelations.Value True, BooleanRelations.ChildOf True root) ->
      -- 1 = slope * root + intercept
      -- =>
      -- root = (1 - intercept) / slope
      Just <$> bindField (B root) ((1 - intercept) / slope) xs
    (BooleanRelations.Value True, BooleanRelations.ChildOf False root) ->
      -- 1 = slope * (1 - root) + intercept
      -- =>
      -- slope * root = slope + intercept - 1
      -- =>
      -- root = (slope + intercept - 1) / slope
      Just <$> bindField (B root) ((slope + intercept - 1) / slope) xs
    (BooleanRelations.Value False, BooleanRelations.Root) ->
      -- 0 = slope * root + intercept
      -- =>
      -- root = - intercept / slope
      Just <$> bindField (B refB) (-intercept / slope) xs
    (BooleanRelations.Value False, BooleanRelations.Value True) ->
      -- 0 = slope * 1 + intercept
      if 0 == slope + intercept then return Nothing else throwError $ ConflictingValuesF 0 (slope + intercept)
    (BooleanRelations.Value False, BooleanRelations.Value False) ->
      if 0 == intercept then return Nothing else throwError $ ConflictingValuesF 0 intercept
    (BooleanRelations.Value False, BooleanRelations.ChildOf True root) ->
      -- 0 = slope * root + intercept
      -- =>
      -- root = - intercept / slope
      Just <$> bindField (B root) (-intercept / slope) xs
    (BooleanRelations.Value False, BooleanRelations.ChildOf False root) ->
      -- 0 = slope * (1 - root) + intercept
      -- =>
      -- slope * root = slope + intercept
      -- =>
      -- root = 1 + intercept / slope
      Just <$> bindField (B root) (1 + intercept / slope) xs
    (BooleanRelations.ChildOf True rootA, BooleanRelations.Root) ->
      -- rootA = slope * rootB + intercept
      relateTwoRefs (B rootA) (slope, B refB, intercept) xs
    (BooleanRelations.ChildOf True rootA, BooleanRelations.Value True) ->
      -- rootA = slope * 1 + intercept
      Just <$> bindField (B rootA) (slope + intercept) xs
    (BooleanRelations.ChildOf True rootA, BooleanRelations.Value False) ->
      Just <$> bindField (B rootA) intercept xs
    (BooleanRelations.ChildOf True rootA, BooleanRelations.ChildOf True rootB) ->
      -- rootA = slope * rootB + intercept
      relateTwoRefs (B rootA) (slope, B rootB, intercept) xs
    (BooleanRelations.ChildOf True rootA, BooleanRelations.ChildOf False rootB) ->
      -- rootA = slope * (1 - rootB) + intercept
      relateTwoRefs (B rootA) (-slope, B rootB, slope + intercept) xs
    (BooleanRelations.ChildOf False rootA, BooleanRelations.Root) ->
      -- rootA = 1 - x && x = slope * y + intercept
      -- =>
      -- rootA = 1 - slope * y - intercept
      relateTwoRefs (B rootA) (-slope, B refB, 1 + intercept) xs
    (BooleanRelations.ChildOf False rootA, BooleanRelations.Value True) ->
      -- rootA = 1 - x && x = slope * 1 + intercept
      -- =>
      -- rootA = 1 - slope - intercept
      Just <$> bindField (B rootA) (1 - slope - intercept) xs
    (BooleanRelations.ChildOf False rootA, BooleanRelations.Value False) ->
      -- rootA = 1 - x && x = slope * 0 + intercept
      -- =>
      -- rootA = 1 - intercept
      Just <$> bindField (B rootA) (1 - intercept) xs
    (BooleanRelations.ChildOf False rootA, BooleanRelations.ChildOf True rootB) ->
      -- rootA = 1 - x && x = slope * rootB + intercept
      -- =>
      -- rootA = 1 - slope * rootB - intercept
      relateTwoRefs (B rootA) (-slope, B rootB, 1 + intercept) xs
    (BooleanRelations.ChildOf False rootA, BooleanRelations.ChildOf False rootB) ->
      -- rootA = 1 - x && x = slope * (1 - rootB) + intercept
      -- =>
      -- rootA = 1 - slope * (1 - rootB) - intercept
      -- =>
      -- rootA = 1 - slope + slope * rootB - intercept
      -- =>
      -- rootA =  slope * rootB  - intercept + 1 - slope
      relateTwoRefs (B rootA) (slope, B rootB, -intercept + 1 - slope) xs

relateTwoRefs :: (GaloisField n, Integral n) => Ref -> (n, Ref, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateTwoRefs x (slope, y, intercept) xs = case compare x y of
  GT -> relateRefF' x (slope, y, intercept) xs -- x = slope * y + intercept
  LT -> relateRefF' y (recip slope, x, -intercept / slope) xs -- y = x / slope - intercept / slope
  EQ -> return Nothing

-- | Establish the relation of 'x = slope * y + intercept'
--   Returns Nothing if the relation has already been established
relateRefF' :: (GaloisField n, Integral n) => Ref -> (n, Ref, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
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
      relateRef rootOfX (slope / slopeX, y, intercept - interceptX / slopeX) xs
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

toMap :: FieldRelations n -> Map Ref (Maybe (n, Ref), n)
toMap = links

size :: FieldRelations n -> Int
size = Map.size . links

exportBooleanRelations :: FieldRelations n -> BooleanRelations
exportBooleanRelations = booleanRelations

exportUIntRelations :: FieldRelations n -> UIntRelations n
exportUIntRelations = uintRelations