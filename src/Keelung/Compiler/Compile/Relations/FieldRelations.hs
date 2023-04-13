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
    -- (F refA, F refB, _, _) -> relateRefFwithRefF refA (slope, refB, intercept) xs
    (F _, F _, _, _) -> relateTwoRefs x (slope, y, intercept) xs
    (F refA, B refB, _, _) -> relateRefFwithRefB'' refA (slope, refB, intercept) xs
    (F refA, U refB, _, _) -> relateRefFwithRefU refA (slope, refB, intercept) xs
    (B refA, F refB, _, _) -> relateRefFwithRefB'' refB (recip slope, refA, -intercept / slope) xs
    (B refA, B refB, _, _) -> relateRefBWithRefB refA (slope, refB, intercept) xs
    (B refA, U refB, _, _) -> relateRefBwithRefU refA (slope, refB, intercept) xs
    (U refA, F refB, _, _) -> relateRefFwithRefU refB (recip slope, refA, -intercept / slope) xs
    (U refA, B refB, _, _) -> relateRefBwithRefU refB (recip slope, refA, -intercept / slope) xs
    (U refA, U refB, _, _) -> relateRefUwithRefU refA (slope, refB, intercept) xs

relateRefFwithRefU :: (GaloisField n, Integral n) => RefT -> (n, RefU, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefFwithRefU refA (slope, refB, intercept) xs = case (parentOf xs (F refA), UIntRelations.lookup (uintRelations xs) refB) of
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

relateRefUwithRefU :: (GaloisField n, Integral n) => RefU -> (n, RefU, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefUwithRefU refA (slope, refB, intercept) xs = case (UIntRelations.lookup (uintRelations xs) refA, UIntRelations.lookup (uintRelations xs) refB) of
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

relateRefBwithRefU :: (GaloisField n, Integral n) => RefB -> (n, RefU, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefBwithRefU refA (slope, refB, intercept) xs = case (BooleanRelations.lookup refA (booleanRelations xs), UIntRelations.lookup (uintRelations xs) refB) of
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

--------------------------------------------------------------------------------

data Relation n = IsRoot Ref | HasValue n | IsChildOf n Ref n

fromBooleanRelation :: (GaloisField n, Integral n) => RefB -> BooleanRelations.Relation -> Relation n
fromBooleanRelation ref BooleanRelations.Root = IsRoot (B ref)
fromBooleanRelation ___ (BooleanRelations.Value True) = HasValue 1
fromBooleanRelation ___ (BooleanRelations.Value False) = HasValue 0
fromBooleanRelation ___ (BooleanRelations.ChildOf True root) = IsChildOf 1 (B root) 0
fromBooleanRelation ___ (BooleanRelations.ChildOf False root) = IsChildOf (-1) (B root) 1

fromFieldRelation :: (GaloisField n, Integral n) => Ref -> Lookup n -> Relation n
fromFieldRelation ref Root = IsRoot ref
fromFieldRelation ___ (Constant n) = HasValue n
fromFieldRelation ___ (ChildOf slope root intercept) = IsChildOf slope root intercept

lookup :: (GaloisField n, Integral n) => Ref -> FieldRelations n -> Relation n
lookup ref xs = fromFieldRelation ref (parentOf xs ref)

composeRelation :: (GaloisField n, Integral n) => FieldRelations n -> n -> n -> Relation n -> Relation n -> Except (Error n) (Maybe (FieldRelations n))
composeRelation xs slope intercept relationA relationB = case (relationA, relationB) of
  (IsRoot rootA, IsRoot rootB) ->
    -- rootA = slope * rootB + intercept
    return $ Just $ relateTwoRefs' rootA (slope, rootB, intercept) xs
  (IsRoot rootA, HasValue n) ->
    -- rootA = slope * n + intercept
    Just <$> bindField rootA (slope * n + intercept) xs
  (IsRoot rootA, IsChildOf slopeB rootB interceptB) ->
    -- rootA = slope * refB + intercept && refB = slopeB * rootB + interceptB
    -- =>
    -- rootA = slope * (slopeB * rootB + interceptB) + intercept
    -- =>
    -- rootA = slope * slopeB * rootB + slope * interceptB + intercept
    return $ Just $ relateTwoRefs' rootA (slope * slopeB, rootB, slope * interceptB + intercept) xs
  (HasValue n, IsRoot rootB) ->
    -- n = slope * rootB + intercept
    -- =>
    -- rootB = (n - intercept) / slope
    Just <$> bindField rootB ((n - intercept) / slope) xs
  (HasValue n, HasValue m) ->
    -- n = slope * m + intercept
    -- =>
    -- n - intercept = slope * m
    -- =>
    -- m = (n - intercept) / slope
    if m == (n - intercept) / slope
      then return Nothing
      else throwError $ ConflictingValuesF m ((n - intercept) / slope)
  (HasValue n, IsChildOf slopeB rootB interceptB) ->
    -- n = slope * (slopeB * rootB + interceptB) + intercept
    -- =>
    -- slope * (slopeB * rootB + interceptB) = n - intercept
    -- =>
    -- slopeB * rootB + interceptB = (n - intercept) / slope
    -- =>
    -- slopeB * rootB = (n - intercept) / slope - interceptB
    -- =>
    -- rootB = ((n - intercept) / slope - interceptB) / slopeB
    Just <$> bindField rootB (((n - intercept) / slope - interceptB) / slopeB) xs
  (IsChildOf slopeA rootA interceptA, IsRoot rootB) ->
    -- refA = slopeA * rootA + interceptA = slope * rootB + intercept
    -- =>
    -- rootA = (slope * rootB + intercept - interceptA) / slopeA
    return $ Just $ relateTwoRefs' rootA (slope / slopeA, rootB, (intercept - interceptA) / slopeA) xs
  (IsChildOf slopeA rootA interceptA, HasValue n) ->
    -- refA = slopeA * rootA + interceptA = slope * n + intercept
    -- =>
    -- rootA = (slope * n + intercept - interceptA) / slopeA
    Just <$> bindField rootA ((slope * n + intercept - interceptA) / slopeA) xs
  (IsChildOf slopeA rootA interceptA, IsChildOf slopeB rootB interceptB) ->
    -- refA = slopeA * rootA + interceptA = slope * (slopeB * rootB + interceptB) + intercept
    -- =>
    -- slopeA * rootA = slope * slopeB * rootB + slope * interceptB + intercept - interceptA
    -- =>
    -- rootA = (slope * slopeB * rootB + slope * interceptB + intercept - interceptA) / slopeA
    return $ Just $ relateTwoRefs' rootA (slope * slopeB / slopeA, rootB, (slope * interceptB + intercept - interceptA) / slopeA) xs

relateTwoRefs' :: (GaloisField n, Integral n) => Ref -> (n, Ref, n) -> FieldRelations n -> FieldRelations n
relateTwoRefs' x (slope, y, intercept) xs = 
  -- case compare x y of
  -- GT -> -- x = slope * y + intercept
  --   xs
  --     { links = Map.insert x (Just (slope, y), intercept) (links xs),
  --       sizes = Map.insertWith (+) y 1 (sizes xs)
  --     }
  -- LT -> relateTwoRefs' y (recip slope, x, -intercept / slope) xs -- y = x / slope - intercept / slope
  -- EQ -> xs

    xs
      { links = Map.insert x (Just (slope, y), intercept) (links xs),
        sizes = Map.insertWith (+) y 1 (sizes xs)
      }

relateRefFwithRefB'' :: (GaloisField n, Integral n) => RefT -> (n, RefB, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefFwithRefB'' refA (slope, refB, intercept) xs =
  composeRelation xs slope intercept (lookup (F refA) xs) (fromBooleanRelation refB (BooleanRelations.lookup refB (booleanRelations xs)))

relateRefFwithRefF :: (GaloisField n, Integral n) => RefT -> (n, RefT, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefFwithRefF refA (slope, refB, intercept) xs =
  composeRelation xs slope intercept (lookup (F refA) xs) (lookup (F refB) xs)

relateRefBWithRefB :: (GaloisField n, Integral n) => RefB -> (n, RefB, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefBWithRefB refA (slope, refB, intercept) xs =
  composeRelation xs slope intercept (fromBooleanRelation refA (BooleanRelations.lookup refA (booleanRelations xs))) (fromBooleanRelation refB (BooleanRelations.lookup refB (booleanRelations xs)))