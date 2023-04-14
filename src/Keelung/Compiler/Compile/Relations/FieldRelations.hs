{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# HLINT ignore "Replace case with fromMaybe" #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Compiler.Compile.Relations.FieldRelations
  ( FieldRelations,
    relationBetween,
    new,
    lookup,
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

-- | Returns 'Nothing' if the variable is already a root.
--   else returns 'Just (slope, root)'  where 'var = slope * root + intercept'
lookup :: Integral n => Ref -> FieldRelations n -> Lookup n
lookup var xs = case Map.lookup var (links xs) of
  Nothing -> IsRoot var -- var is a root
  Just (Nothing, intercept) -> HasValue intercept -- var is a root
  Just (Just (slope, parent), intercept) -> case lookup parent xs of
    IsRoot _ ->
      -- parent is a root
      IsChildOf slope parent intercept
    HasValue intercept' ->
      -- parent is a value
      -- var = slope * parent + intercept
      -- parent = intercept'
      --  =>
      -- var = slope * intercept' + intercept
      HasValue (slope * intercept' + intercept)
    IsChildOf slope' grandparent intercept' ->
      -- var = slope * parent + intercept
      -- parent = slope' * grandparent + intercept'
      --  =>
      -- var = slope * (slope' * grandparent + intercept') + intercept
      --  =>
      -- var = slope * slope' * grandparent + slope * intercept' + intercept
      IsChildOf (slope * slope') grandparent (slope * intercept' + intercept)

-- | Calculates the relation between two variables `var1` and `var2`
--   Returns `Nothing` if the two variables are not related.
--   Returns `Just (slope, intercept)` where `var1 = slope * var2 + intercept` if the two variables are related.
relationBetween :: (GaloisField n, Integral n) => Ref -> Ref -> FieldRelations n -> Maybe (n, n)
relationBetween var1 var2 xs = case (lookup var1 xs, lookup var2 xs) of
  (IsRoot _, IsRoot _) ->
    if var1 == var2
      then Just (1, 0)
      else Nothing -- var1 and var2 are roots, but not the same one
  (IsRoot _, IsChildOf slope2 root2 intercept2) ->
    -- var2 = slope2 * root2 + intercept2
    --  =>
    -- root2 = (var2 - intercept2) / slope2
    if var1 == root2
      then -- var1 = root2
      --  =>
      -- var1 = (var2 - intercept2) / slope2
        Just (recip slope2, -intercept2 / slope2)
      else Nothing
  (IsRoot _, HasValue _) -> Nothing -- var1 is a root, var2 is a value
  (IsChildOf slope1 root1 intercept1, IsRoot _) ->
    -- var1 = slope1 * root1 + intercept1
    if var2 == root1
      then -- var2 = root1
      --  =>
      -- var1 = slope1 * var2 + intercept1
        Just (slope1, intercept1)
      else Nothing
  (HasValue _, IsRoot _) -> Nothing -- var1 is a value, var2 is a root
  (IsChildOf slope1 root1 intercept1, IsChildOf slope2 root2 intercept2) ->
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
  (IsChildOf {}, HasValue _) -> Nothing -- var2 is a value
  (HasValue _, IsChildOf {}) -> Nothing -- var1 is a value
  (HasValue x, HasValue y) ->
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
      case lookup x xs of
        IsRoot _ ->
          -- x does not have a parent, so it is its own root
          return $
            xs
              { links = Map.insert x (Nothing, value) (links xs),
                sizes = Map.insert x 1 (sizes xs)
              }
        HasValue oldValue ->
          if oldValue == value
            then
              return $
                xs
                  { links = Map.insert x (Nothing, value) (links xs)
                  }
            else throwError $ ConflictingValuesF oldValue value
        IsChildOf slopeP parent interceptP ->
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
    (F refA, U refB, _, _) -> relateRefFWithRefU refA (slope, refB, intercept) xs
    (B refA, F refB, _, _) -> relateRefFwithRefB'' refB (recip slope, refA, -intercept / slope) xs
    (B refA, B refB, _, _) -> relateRefBWithRefB refA (slope, refB, intercept) xs
    (B refA, U refB, _, _) -> relateRefBWithRefU refA (slope, refB, intercept) xs
    (U refA, F refB, _, _) -> relateRefFWithRefU refB (recip slope, refA, -intercept / slope) xs
    (U refA, B refB, _, _) -> relateRefBWithRefU refB (recip slope, refA, -intercept / slope) xs
    (U refA, U refB, _, _) -> relateRefUWithRefU refA (slope, refB, intercept) xs

relateTwoRefs :: (GaloisField n, Integral n) => Ref -> (n, Ref, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateTwoRefs x (slope, y, intercept) xs = case compare x y of
  GT -> relateRefF' x (slope, y, intercept) xs -- x = slope * y + intercept
  LT -> relateRefF' y (recip slope, x, -intercept / slope) xs -- y = x / slope - intercept / slope
  EQ -> return Nothing

-- | Establish the relation of 'x = slope * y + intercept'
--   Returns Nothing if the relation has already been established
relateRefF' :: (GaloisField n, Integral n) => Ref -> (n, Ref, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefF' x (slope, y, intercept) xs =
  case lookup x xs of
    HasValue interceptX ->
      -- x is already a root with `interceptX` as its value
      --  x = slope * y + intercept
      --  x = interceptX
      -- =>
      --  slope * y + intercept = interceptX
      -- =>
      --  y = (interceptX - intercept) / slope
      Just <$> bindField y (interceptX - intercept / slope) xs
    IsChildOf slopeX rootOfX interceptX ->
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
    IsRoot _ ->
      -- x does not have a parent, so it is its own root
      case lookup y xs of
        HasValue interceptY ->
          -- y is already a root with `interceptY` as its value
          --  x = slope * y + intercept
          --  y = interceptY
          -- =>
          --  x = slope * interceptY + intercept
          Just <$> bindField x (slope * interceptY + intercept) xs
        IsChildOf slopeY rootOfY interceptY ->
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
        IsRoot _ ->
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

data Lookup n = IsRoot Ref | HasValue n | IsChildOf n Ref n
  deriving (Eq, Show)

fromBooleanLookup :: (GaloisField n, Integral n) => RefB -> BooleanRelations.Lookup -> Lookup n
fromBooleanLookup ref BooleanRelations.Root = IsRoot (B ref)
fromBooleanLookup ___ (BooleanRelations.Value True) = HasValue 1
fromBooleanLookup ___ (BooleanRelations.Value False) = HasValue 0
fromBooleanLookup ___ (BooleanRelations.ChildOf True root) = IsChildOf 1 (B root) 0
fromBooleanLookup ___ (BooleanRelations.ChildOf False root) = IsChildOf (-1) (B root) 1

fromUIntLookup :: (GaloisField n, Integral n) => RefU -> UIntRelations.Lookup n -> Lookup n
fromUIntLookup ref UIntRelations.Root = IsRoot (U ref)
fromUIntLookup ___ (UIntRelations.Value n) = HasValue n
fromUIntLookup ___ (UIntRelations.RotateOf 0 root) = IsChildOf 1 (U root) 0
fromUIntLookup ___ (UIntRelations.RotateOf _rotation _root) = error "[ panic ]: Don't know how to relate a field to a rotated UInt"

composeLookup :: (GaloisField n, Integral n) => FieldRelations n -> n -> n -> Lookup n -> Lookup n -> Except (Error n) (Maybe (FieldRelations n))
composeLookup xs slope intercept relationA relationB = case (relationA, relationB) of
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
  composeLookup xs slope intercept (lookup (F refA) xs) (fromBooleanLookup refB (BooleanRelations.lookup refB (booleanRelations xs)))

_relateRefFwithRefF :: (GaloisField n, Integral n) => RefT -> (n, RefT, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
_relateRefFwithRefF refA (slope, refB, intercept) xs =
  composeLookup xs slope intercept (lookup (F refA) xs) (lookup (F refB) xs)

relateRefBWithRefB :: (GaloisField n, Integral n) => RefB -> (n, RefB, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefBWithRefB refA (slope, refB, intercept) xs =
  composeLookup xs slope intercept (fromBooleanLookup refA (BooleanRelations.lookup refA (booleanRelations xs))) (fromBooleanLookup refB (BooleanRelations.lookup refB (booleanRelations xs)))

relateRefFWithRefU :: (GaloisField n, Integral n) => RefT -> (n, RefU, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefFWithRefU refA (slope, refB, intercept) xs =
  composeLookup xs slope intercept (lookup (F refA) xs) (fromUIntLookup refB (UIntRelations.lookup (uintRelations xs) refB))

relateRefUWithRefU :: (GaloisField n, Integral n) => RefU -> (n, RefU, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefUWithRefU refA (slope, refB, intercept) xs =
  composeLookup xs slope intercept (fromUIntLookup refA (UIntRelations.lookup (uintRelations xs) refA)) (fromUIntLookup refB (UIntRelations.lookup (uintRelations xs) refB))

relateRefBWithRefU :: (GaloisField n, Integral n) => RefB -> (n, RefU, n) -> FieldRelations n -> Except (Error n) (Maybe (FieldRelations n))
relateRefBWithRefU refA (slope, refB, intercept) xs =
  composeLookup xs slope intercept (fromBooleanLookup refA (BooleanRelations.lookup refA (booleanRelations xs))) (fromUIntLookup refB (UIntRelations.lookup (uintRelations xs) refB))