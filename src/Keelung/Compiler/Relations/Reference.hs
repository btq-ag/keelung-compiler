{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Relations.Reference
  ( RefRelations,
    new,
    assignR,
    relateB,
    relateR,
    relationBetween,
    toConstraints,
    lookup,
    Lookup (..),
  )
where

import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Relations.Slice (SliceRelations)
import Keelung.Compiler.Relations.Slice qualified as SliceRelations
import Keelung.Data.Constraint
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Prelude hiding (lookup)

type RefRelations n = EquivClass.EquivClass n

--------------------------------------------------------------------------------

new :: RefRelations n
new = EquivClass.new "References Relations"

-- | Note: `RefUBit` should not be allowed here
assignR :: (GaloisField n, Integral n) => Ref -> n -> RefRelations n -> EquivClass.M n (RefRelations n)
assignR = EquivClass.assign

relateB :: (GaloisField n, Integral n) => RefB -> (Bool, RefB) -> RefRelations n -> EquivClass.M n (RefRelations n)
relateB refA (polarity, refB) = EquivClass.relate (B refA) (if polarity then EquivClass.LinRel 1 0 else EquivClass.LinRel (-1) 1) (B refB)

-- var = slope * var2 + intercept
relateR :: (GaloisField n, Integral n) => SliceRelations -> Ref -> n -> Ref -> n -> RefRelations n -> EquivClass.M n (RefRelations n)
relateR relationsS x slope y intercept xs =
  case (x, y, slope, intercept) of
    (_, _, 0, value) -> assignR x value xs
    (refA, refB, _, _) ->
      composeLookup
        xs
        refA
        refB
        slope
        intercept
        (lookup relationsS refA xs)
        (lookup relationsS refB xs)

relationBetween :: (GaloisField n, Integral n) => Ref -> Ref -> RefRelations n -> Maybe (n, n)
relationBetween var1 var2 xs = case EquivClass.relationBetween var1 var2 xs of
  Nothing -> Nothing
  Just (EquivClass.LinRel a b) -> Just (a, b)

-- | Convert the relations to specialized constraints
toConstraints :: (GaloisField n, Integral n) => (Ref -> Bool) -> RefRelations n -> Seq (Constraint n)
toConstraints shouldBeKept = Seq.fromList . toList . Map.mapMaybeWithKey convert . EquivClass.toMap
  where
    convert :: (GaloisField n, Integral n) => Ref -> EquivClass.VarStatus n -> Maybe (Constraint n)
    convert var status
      | shouldBeKept var = case status of
          EquivClass.IsConstant val -> Just (CRefFVal var val)
          EquivClass.IsRoot _ -> Nothing
          EquivClass.IsChildOf parent (EquivClass.LinRel slope intercept) ->
            if shouldBeKept parent
              then case (slope, intercept) of
                (0, _) -> Just (CRefFVal var intercept)
                (1, 0) -> Just (CRefEq var parent)
                (_, _) -> case PolyL.fromRefs intercept [(var, -1), (parent, slope)] of
                  Left _ -> error "[ panic ] extractRefRelations: failed to build polynomial"
                  Right poly -> Just (CAddL poly)
              else Nothing
      | otherwise = Nothing

--------------------------------------------------------------------------------

-- | Result of looking up a variable in the Relations
data Lookup n = Root | Value n | ChildOf n Ref n
  deriving
    ( -- | ChildOfU RefU
      Eq,
      Show
    )

lookup :: (GaloisField n) => SliceRelations -> Ref -> RefRelations n -> Lookup n
lookup relationsS (B (RefUBit refU index)) relationsR =
  let -- look in the SliceRelations first
      lookupSliceRelations = case SliceRelations.refUSegmentsRefUBit refU index relationsS of
        Nothing -> lookupRefRelations
        Just (Left (parent, index')) -> ChildOf 1 (B (RefUBit parent index')) 0
        Just (Right bitVal) -> Value (if bitVal then 1 else 0)
      -- look in the RefRelations later if we cannot find any result in the SliceRelations
      lookupRefRelations = case EquivClass.lookup (B (RefUBit refU index)) relationsR of
        EquivClass.IsConstant value -> Value value
        EquivClass.IsRoot _ -> Root
        EquivClass.IsChildOf parent (EquivClass.LinRel a b) -> ChildOf a parent b
   in lookupSliceRelations
lookup _ var relations =
  case EquivClass.lookup var relations of
    EquivClass.IsConstant value -> Value value
    EquivClass.IsRoot _ -> Root
    EquivClass.IsChildOf parent (EquivClass.LinRel a b) -> ChildOf a parent b

--------------------------------------------------------------------------------

composeLookup :: (GaloisField n, Integral n) => RefRelations n -> Ref -> Ref -> n -> n -> Lookup n -> Lookup n -> EquivClass.M n (RefRelations n)
composeLookup xs refA refB slope intercept relationA relationB = case (relationA, relationB) of
  (Root, Root) ->
    -- rootA = slope * rootB + intercept
    relateF refA slope refB intercept xs
  (Root, Value n) ->
    -- rootA = slope * n + intercept
    assignR refA (slope * n + intercept) xs
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
    assignR refB ((n - intercept) / slope) xs
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
    assignR rootB (((n - intercept) / slope - interceptB) / slopeB) xs
  (ChildOf slopeA rootA interceptA, Root) ->
    -- refA = slopeA * rootA + interceptA = slope * rootB + intercept
    -- =>
    -- rootA = (slope * rootB + intercept - interceptA) / slopeA
    relateF rootA (slope / slopeA) refB ((intercept - interceptA) / slopeA) xs
  (ChildOf slopeA rootA interceptA, Value n) ->
    -- refA = slopeA * rootA + interceptA = slope * n + intercept
    -- =>
    -- rootA = (slope * n + intercept - interceptA) / slopeA
    assignR rootA ((slope * n + intercept - interceptA) / slopeA) xs
  (ChildOf slopeA rootA interceptA, ChildOf slopeB rootB interceptB) ->
    -- refA = slopeA * rootA + interceptA = slope * (slopeB * rootB + interceptB) + intercept
    -- =>
    -- slopeA * rootA = slope * slopeB * rootB + slope * interceptB + intercept - interceptA
    -- =>
    -- rootA = (slope * slopeB * rootB + slope * interceptB + intercept - interceptA) / slopeA
    relateF rootA (slope * slopeB / slopeA) rootB ((slope * interceptB + intercept - interceptA) / slopeA) xs
  where
    relateF :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> RefRelations n -> EquivClass.M n (RefRelations n)
    relateF var1 slope' var2 intercept' = EquivClass.relate var1 (EquivClass.LinRel slope' intercept') var2
