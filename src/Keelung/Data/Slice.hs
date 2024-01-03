module Keelung.Data.Slice
  ( Slices (..),
    Slice (..),
    fromRefU,
    split,

    -- * Merging
    MergeError (..),
    merge,
    safeMerge,
  )
where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Keelung (HasWidth, widthOf)
import Keelung.Data.Limb (Limb)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference (RefU)
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U

--------------------------------------------------------------------------------

-- | A slice of a `RefU`
data Slice
  = Constant U
  | ChildOf Limb -- it's a child of another
  | Parent Int --  here stores the length of this Slice
  deriving (Eq)

instance Show Slice where
  show (Constant u) = "Constant[" <> show (widthOf u) <> "] " <> show u
  show (ChildOf limb) = "ChildOf[" <> show (widthOf limb) <> "] " <> show limb
  show (Parent len) = "Parent[" <> show len <> "]"

instance HasWidth Slice where
  widthOf (Constant u) = widthOf u
  widthOf (ChildOf limb) = widthOf limb
  widthOf (Parent len) = len

-- | Non-overlapping Slices of a RefU.
data Slices = Slices
  { slicesRefU :: RefU, -- the `RefU` this series of slices belongs to
    slicesOffset :: Int, -- the starting offset of the first slice
    slicesElems :: IntMap Slice -- the slices
  }
  -- slices indexed by their starting offsets
  deriving (Eq)

instance Show Slices where
  show (Slices ref offset xs) = "Slices " <> show ref <> " " <> show offset <> " " <> show (IntMap.toList xs)

instance HasWidth Slices where
  widthOf (Slices _ offset xs) = case IntMap.lookupMax xs of
    Nothing -> 0
    Just (index, slice) -> index + widthOf slice - offset

instance Semigroup Slices where
  (<>) = merge

--------------------------------------------------------------------------------

-- | Constructs a `Slice` with a `RefU` as its own parent
fromRefU :: RefU -> Slices
fromRefU ref = Slices ref 0 (IntMap.singleton 0 (Parent (widthOf ref)))

-- | Split a `Slice` into two at a given index
splitSlice :: Int -> Slice -> (Slice, Slice)
splitSlice index slice = case slice of
  Constant val -> (Constant (U.slice val 0 index), Constant (U.slice val index (widthOf val - index)))
  ChildOf limb -> let (limb1, limb2) = Limb.split index limb in (ChildOf limb1, ChildOf limb2)
  Parent len -> (Parent index, Parent (len - index))

-- | Split a `Slices` into two at a given index
split :: Int -> Slices -> (Slices, Slices)
split index (Slices ref offset xs) = case IntMap.splitLookup index xs of
  (before, Just slice, after) -> (Slices ref offset before, Slices ref index (IntMap.insert index slice after))
  (before, Nothing, after) -> case IntMap.lookupLE index xs of
    Nothing -> (Slices ref offset mempty, Slices ref offset after)
    Just (index', slice) ->
      let (slice1, slice2) = splitSlice (index - index') slice
       in (Slices ref offset (IntMap.insert index' slice1 before), Slices ref index (IntMap.insert index slice2 after))

--------------------------------------------------------------------------------

-- | Merging two Slices
data MergeError
  = NotSameRefU -- two `Slices` are not of the same `RefU`
  | NotAdjacent -- two `Slices` are not adjacent
  | Overlapping -- two `Slices` are overlapping
  | CannotMergeLimbs
  deriving (Eq)

instance Show MergeError where
  show NotSameRefU = "Slice.MergeError: two slices are not of the same RefU"
  show NotAdjacent = "Slice.MergeError: two slices are not adjacent with each other"
  show Overlapping = "Slice.MergeError: two slices are overlapping with each other"
  show CannotMergeLimbs = "Slice.MergeError: cannot merge two Limbs together"

-- | Merge two `Slices` into one, throwing MergeError if the slices are:
--    1. not of the same `RefU`
--    2. not adjacent
--    3. overlapping
safeMerge :: Slices -> Slices -> Either MergeError Slices
safeMerge slice1@(Slices ref1 offset1 xs1) (Slices ref2 offset2 xs2)
  | ref1 /= ref2 = Left NotSameRefU
  | otherwise = case (offset1 + widthOf slice1) `compare` offset2 of
      LT -> Left NotAdjacent
      GT -> Left Overlapping
      EQ -> case xs1 `glueSliceIntMap` xs2 of
        Left _ -> Left CannotMergeLimbs
        Right result -> Right (Slices ref1 offset1 result)

-- | Unsafe version of `safeMerge`
merge :: Slices -> Slices -> Slices
merge xs ys = case safeMerge xs ys of
  Left err -> error $ "[ panic ] " <> show err
  Right result -> result

-- | Merge two `IntMap Slice` and see of both ends can be glued together
glueSliceIntMap :: IntMap Slice -> IntMap Slice -> Either Limb.MergeError (IntMap Slice)
glueSliceIntMap xs ys = case (IntMap.maxViewWithKey xs, IntMap.minView ys) of
  (Just ((index1, slice1), xs'), Just (slice2, ys')) -> case (slice1, slice2) of
    (Constant val1, Constant val2) -> Right $ IntMap.insert index1 (Constant (val2 <> val1)) (xs' <> ys')
    (ChildOf limb, ChildOf limb') -> case Limb.safeMerge limb limb' of
      Left err -> Left err
      Right limb'' -> Right $ IntMap.insert index1 (ChildOf limb'') (xs' <> ys')
    (Parent len, Parent len') -> Right $ IntMap.insert index1 (Parent (len + len')) (xs' <> ys')
    _ -> Right $ xs <> ys
  _ -> Right $ xs <> ys