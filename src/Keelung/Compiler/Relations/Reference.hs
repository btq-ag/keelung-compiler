{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Relations.Reference
  ( RefRelations,
    new,
    assignF,
    relateB,
    relateR,
    relationBetween,
    toInt,
    lookup,
    Lookup (..),
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Keelung (N (N))
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Options
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Relations.UInt (UIntRelations)
import Keelung.Compiler.Relations.UInt qualified as UInt
import Keelung.Data.Reference
import Prelude hiding (lookup)

type RefRelations n = EquivClass.EquivClass Ref n (LinRel n)

mapError :: EquivClass.M (n, n) a -> EquivClass.M (Error n) a
mapError = EquivClass.mapError (uncurry ConflictingValuesF)

--------------------------------------------------------------------------------

new :: RefRelations n
new = EquivClass.new "References Relations"

assignF :: (GaloisField n, Integral n) => Ref -> n -> RefRelations n -> EquivClass.M (Error n) (RefRelations n)
assignF var val xs = mapError $ EquivClass.assign var val xs

relateB :: (GaloisField n, Integral n) => (GaloisField n) => RefB -> (Bool, RefB) -> RefRelations n -> EquivClass.M (Error n) (RefRelations n)
relateB refA (polarity, refB) xs = mapError $ EquivClass.relate (B refA) (if polarity then LinRel 1 0 else LinRel (-1) 1) (B refB) xs

-- var = slope * var2 + intercept
relateR :: (GaloisField n, Integral n) => Options -> UIntRelations -> Ref -> n -> Ref -> n -> RefRelations n -> EquivClass.M (Error n) (RefRelations n)
relateR options relationsU x slope y intercept xs =
  case (x, y, slope, intercept) of
    (_, _, 0, value) -> assignF x value xs
    (refA, refB, _, _) ->
      composeLookup
        xs
        refA
        refB
        slope
        intercept
        (lookup options relationsU refA xs)
        (lookup options relationsU refB xs)

relationBetween :: (GaloisField n, Integral n) => Ref -> Ref -> RefRelations n -> Maybe (n, n)
relationBetween var1 var2 xs = case EquivClass.relationBetween var1 var2 xs of
  Nothing -> Nothing
  Just (LinRel a b) -> Just (a, b)

toInt :: (Ref -> Bool) -> RefRelations n -> Map Ref (Either (n, Ref, n) n)
toInt shouldBeKept xs = Map.mapMaybeWithKey convert $ EquivClass.toMap xs
  where
    convert var status = do
      if shouldBeKept var
        then case status of
          EquivClass.IsConstant val -> Just (Right val)
          EquivClass.IsRoot _ -> Nothing
          EquivClass.IsChildOf parent (LinRel slope intercept) ->
            if shouldBeKept parent
              then Just $ Left (slope, parent, intercept)
              else Nothing
        else Nothing

--------------------------------------------------------------------------------

-- | Result of looking up a variable in the Relations
data Lookup n = Root | Value n | ChildOf n Ref n
  deriving
    ( -- | ChildOfU RefU
      Eq,
      Show
    )

lookup :: (GaloisField n) => Options -> UIntRelations -> Ref -> RefRelations n -> Lookup n
lookup _options relationsU (B (RefUBit refU index)) _relations = case EquivClass.lookup (UInt.Ref refU) relationsU of
  EquivClass.IsConstant value -> Value (if Data.Bits.testBit value index then 1 else 0)
  EquivClass.IsRoot toChildren ->
    if Map.null toChildren
      then -- cannot find any result in the UIntRelations, so we look in the RefRelations instead
      case EquivClass.lookup (B (RefUBit refU index)) _relations of
        EquivClass.IsConstant value -> Value value
        EquivClass.IsRoot _ -> Root
        EquivClass.IsChildOf parent (LinRel a b) -> ChildOf a parent b
      else Root
  EquivClass.IsChildOf (UInt.Ref parent) UInt.Equal -> ChildOf 1 (B (RefUBit parent index)) 0
-- EquivClass.IsChildOf parent (UInt.ShiftLeft 0) -> ChildOf 1 (B (RefUBit parent index)) 0
-- EquivClass.IsChildOf parent (UInt.ShiftLeft n) ->
--     -- parent  ┌─┬─┬─┬─┬─┬─┬─┬─┐
--     --         └─┴─┴─┴─┴─┴─┴─┴─┘
--     --                  │
--     --              ┌───┘  shift left by n bits
--     --              ▼
--     -- refU    ┌─┬─┬─┬─┬─┬─┬─┬─┐
--     --         └─┴─┴─┴─┴─┴─┴─┴─┘
--     if index < n
--       then Value 0 -- zeroed out
--       else ChildOf 1 (B (RefUBit parent (index - n))) 0
lookup _ _ var relations = case EquivClass.lookup var relations of
  EquivClass.IsConstant value -> Value value
  EquivClass.IsRoot _ -> Root
  EquivClass.IsChildOf parent (LinRel a b) -> ChildOf a parent b

-- fromBooleanLookup :: GaloisField n => EquivClass.VarStatus RefB Bool Boolean.Polarity -> EquivClass.VarStatus Ref n (LinRel n)
-- fromBooleanLookup (EquivClass.IsRoot children) = EquivClass.IsRoot $ Map.mapKeys B $ Map.map (\b -> if Boolean.unPolarity b then LinRel 1 0 else LinRel (-1) 1) children

--------------------------------------------------------------------------------

-- | Relation representing a linear function between two variables, i.e. x = ay + b
data LinRel n
  = LinRel
      n
      -- | slope
      n
  deriving
    ( -- | intercept
      Show,
      Eq,
      NFData,
      Generic
    )

instance (Num n) => Semigroup (LinRel n) where
  -- x = a1 * y + b1
  -- y = a2 * z + b2
  -- =>
  -- x = a1 * (a2 * z + b2) + b1
  --   = (a1 * a2) * z + (a1 * b2 + b1)
  LinRel a1 b1 <> LinRel a2 b2 = LinRel (a1 * a2) (a1 * b2 + b1)

instance (Num n) => Monoid (LinRel n) where
  mempty = LinRel 1 0

instance (GaloisField n, Integral n) => EquivClass.IsRelation (LinRel n) where
  relationToString (var, LinRel x y) = go (LinRel (recip x) (-y / x))
    where
      go (LinRel (-1) 1) = "¬" <> var
      go (LinRel a b) =
        let slope = case a of
              1 -> var
              (-1) -> "-" <> var
              _ -> show (N a) <> var
            intercept = case b of
              0 -> ""
              _ -> " + " <> show (N b)
         in slope <> intercept

  -- x = ay + b
  -- =>
  -- y = (x - b) / a
  invertRel (LinRel a b) = Just (LinRel (recip a) (-b / a))

instance (GaloisField n, Integral n) => EquivClass.ExecRelation n (LinRel n) where
  execRel (LinRel a b) value = a * value + b

--------------------------------------------------------------------------------

composeLookup :: (GaloisField n, Integral n) => RefRelations n -> Ref -> Ref -> n -> n -> Lookup n -> Lookup n -> EquivClass.M (Error n) (RefRelations n)
composeLookup xs refA refB slope intercept relationA relationB = case (relationA, relationB) of
  (Root, Root) ->
    -- rootA = slope * rootB + intercept
    relateF refA slope refB intercept xs
  (Root, Value n) ->
    -- rootA = slope * n + intercept
    assignF refA (slope * n + intercept) xs
  (Root, ChildOf slopeB rootB interceptB) ->
    -- rootA = slope * refB + intercept && refB = slopeB * rootB + interceptB
    -- =>
    -- rootA = slope * (slopeB * rootB + interceptB) + intercept
    -- =>
    -- rootA = slope * slopeB * rootB + slope * interceptB + intercept
    relateF refA (slope * slopeB) rootB (slope * interceptB + intercept) xs
  (Value n, Root) ->
    -- n = slope * rootB + intercept
    -- =>
    -- rootB = (n - intercept) / slope
    assignF refB ((n - intercept) / slope) xs
  (Value n, Value m) ->
    -- n = slope * m + intercept
    -- =>
    -- n - intercept = slope * m
    -- =>
    -- m = (n - intercept) / slope
    if m == (n - intercept) / slope
      then return xs
      else throwError $ ConflictingValuesF m ((n - intercept) / slope)
  (Value n, ChildOf slopeB rootB interceptB) ->
    -- n = slope * (slopeB * rootB + interceptB) + intercept
    -- =>
    -- slope * (slopeB * rootB + interceptB) = n - intercept
    -- =>
    -- slopeB * rootB + interceptB = (n - intercept) / slope
    -- =>
    -- slopeB * rootB = (n - intercept) / slope - interceptB
    -- =>
    -- rootB = ((n - intercept) / slope - interceptB) / slopeB
    assignF rootB (((n - intercept) / slope - interceptB) / slopeB) xs
  (ChildOf slopeA rootA interceptA, Root) ->
    -- refA = slopeA * rootA + interceptA = slope * rootB + intercept
    -- =>
    -- rootA = (slope * rootB + intercept - interceptA) / slopeA
    relateF rootA (slope / slopeA) refB ((intercept - interceptA) / slopeA) xs
  (ChildOf slopeA rootA interceptA, Value n) ->
    -- refA = slopeA * rootA + interceptA = slope * n + intercept
    -- =>
    -- rootA = (slope * n + intercept - interceptA) / slopeA
    assignF rootA ((slope * n + intercept - interceptA) / slopeA) xs
  (ChildOf slopeA rootA interceptA, ChildOf slopeB rootB interceptB) ->
    -- refA = slopeA * rootA + interceptA = slope * (slopeB * rootB + interceptB) + intercept
    -- =>
    -- slopeA * rootA = slope * slopeB * rootB + slope * interceptB + intercept - interceptA
    -- =>
    -- rootA = (slope * slopeB * rootB + slope * interceptB + intercept - interceptA) / slopeA
    relateF rootA (slope * slopeB / slopeA) rootB ((slope * interceptB + intercept - interceptA) / slopeA) xs
  where
    relateF :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> RefRelations n -> EquivClass.M (Error n) (RefRelations n)
    relateF var1 slope' var2 intercept' xs' = mapError $ EquivClass.relate var1 (LinRel slope' intercept') var2 xs'
