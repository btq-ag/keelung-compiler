{-# LANGUAGE DeriveGeneric #-}

module Keelung.Data.Slice
  ( -- * Construction
    Slice (..),
    fromRefU,
    fromRefUWithDesiredWidth,

    -- * Conversion

    -- fromLimb,
    fromLimb,
    fromLimbWithValue,
    toLimb,

    -- * Predicates
    null,
    overlaps,

    -- * Operations
    SplitError (..),
    safeSplit,
    split,
    MergeError (..),
    safeMerge,
    merge,
  )
where

import Control.DeepSeq (NFData)
import Data.Bits qualified
import GHC.Generics (Generic)
import Keelung (HasWidth, widthOf)
import Keelung.Data.Limb (Limb)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference (RefU (..))
import Keelung.Syntax (Width)
import Prelude hiding (map, null)

--------------------------------------------------------------------------------

-- | A "Slice" of a RefU
data Slice = Slice
  { sliceRefU :: RefU, -- the `RefU` this slice belongs to
    sliceStart :: Int, -- the starting offset of the slice
    sliceEnd :: Int -- the ending offset of the slice
  }
  deriving (Eq, Generic)

instance NFData Slice

instance Show Slice where
  show (Slice ref start end) = show ref <> " [" <> show start <> " ... " <> show end <> ")"

instance HasWidth Slice where
  widthOf (Slice _ start end) = end - start

-- | A Slice gets to be the root in UnionFind if:
--    1. it has "larger" RefU
--    2. it has "smaller" offsets
instance Ord Slice where
  (Slice ref1 start1 end1) `compare` (Slice ref2 start2 end2) = compare ref1 ref2 <> compare start2 start1 <> compare end2 end1

instance Semigroup Slice where
  (<>) = merge

--------------------------------------------------------------------------------

-- | Construct a "Slice" from a "RefU" that covers its entire width
fromRefU :: RefU -> Slice
fromRefU ref = Slice ref 0 (widthOf ref)

-- | Construct "Slice"s from a "RefU" with a desired width
fromRefUWithDesiredWidth :: Width -> RefU -> [Slice]
fromRefUWithDesiredWidth width refU =
  if width > 0
    then [Slice refU i ((i + width) `min` widthOf refU) | i <- [0, width .. widthOf refU - 1]]
    else error "[ panic ] Slice.fromRefUWithDesiredWidth: desired width must be positive"

-- | Construct a "Slice" from a "RefU" and an index
fromRefUBit :: RefU -> Int -> Slice
fromRefUBit ref i = Slice ref i (i + 1)

-- | Construct "Slice"s from a "Limb" with a list of coeffients
fromLimb :: Limb -> [(Integer, Slice)]
fromLimb limb = case Limb.lmbSigns limb of
  Left sign -> [(if sign then 1 else -1, Slice (Limb.lmbRef limb) (Limb.lmbOffset limb) (Limb.lmbOffset limb + widthOf limb))]
  Right signs ->
    [ (if sign then 2 ^ i else -(2 ^ i), fromRefUBit (Limb.lmbRef limb) (i + Limb.lmbOffset limb))
      | (i, sign) <- zip [0 .. widthOf limb - 1] signs
    ]

-- | Like "fromLimb", but pairs the slices with chunks of the value adjusted by the signs
fromLimbWithValue :: Limb -> Integer -> [(Slice, Integer)]
fromLimbWithValue limb val = case Limb.lmbSigns limb of
  Left sign -> [(Slice (Limb.lmbRef limb) (Limb.lmbOffset limb) (Limb.lmbOffset limb + widthOf limb), if sign then val else -val)]
  Right signs ->
    [ let bit = Data.Bits.testBit val (offset - Limb.lmbOffset limb)
       in (fromRefUBit (Limb.lmbRef limb) offset, if Data.Bits.xor sign bit then 1 else 0)
      | (offset, sign) <- zip [Limb.lmbOffset limb .. Limb.lmbOffset limb + widthOf limb - 1] signs
    ]

-- | Convert a "Slice" to a "Limb"
toLimb :: Slice -> Limb
toLimb (Slice ref start end) = Limb.new ref (end - start) start (Left True)

--------------------------------------------------------------------------------

null :: Slice -> Bool
null (Slice _ start end) = start == end

overlaps :: Slice -> Slice -> Bool
overlaps (Slice ref1 start1 end1) (Slice ref2 start2 end2) =
  ref1 == ref2
    && ( (start1 < end2 && start2 < end1)
           || (start2 < end1 && start1 < end2)
       )

--------------------------------------------------------------------------------

data SplitError = OffsetOutOfBound
  deriving (Eq)

instance Show SplitError where
  show OffsetOutOfBound = "Slice.SplitError: offset out of bound"

-- | Split a 'Slice' into two 'Slice's at a given index (the index is relative to the starting offset of the Slice)
safeSplit :: Int -> Slice -> Either SplitError (Slice, Slice)
safeSplit index (Slice ref start end)
  | index < 0 || index > end - start = Left OffsetOutOfBound
  | otherwise =
      Right
        ( Slice ref start (start + index),
          Slice ref (start + index) end
        )

-- | Unsafe version of 'safeSplit'
split :: Int -> Slice -> (Slice, Slice)
split index slice = case safeSplit index slice of
  Left err -> error $ "[ panic ] " <> show err
  Right result -> result

--------------------------------------------------------------------------------

-- | Unsafe version of 'merge'
merge :: Slice -> Slice -> Slice
merge slice1 slice2 = case safeMerge slice1 slice2 of
  Left err -> error $ "[ panic ] " <> show err
  Right slice -> slice

data MergeError = NotSameRefU | NotAdjacent | Overlapping
  deriving (Eq, Ord)

instance Show MergeError where
  show NotSameRefU = "Slice.MergeError: two slices are not of the same RefU"
  show NotAdjacent = "Slice.MergeError: two slices are not adjacent with each other"
  show Overlapping = "Slice.MergeError: two slices are overlapping with each other"

-- | Merge two Slices into one, throwing MergeError if:
--    1. the two Slices are not of the same `RefU`
--    2. the two Slices are not adjacent
--    3. the two Slices are overlapping
safeMerge :: Slice -> Slice -> Either MergeError Slice
safeMerge (Slice ref1 start1 end1) (Slice ref2 start2 end2)
  | ref1 /= ref2 = Left NotSameRefU
  | otherwise = case end1 `compare` start2 of
      LT -> Left NotAdjacent
      GT -> Left Overlapping
      EQ -> Right $ Slice ref1 start1 end2