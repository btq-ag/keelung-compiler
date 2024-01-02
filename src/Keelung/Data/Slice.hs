module Keelung.Data.Slice (Slices (..), Slice (..), RefUSlices (..), new, split, splitSlices) where

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

instance HasWidth Slices where
  widthOf (Slices offset xs) = case IntMap.lookupMax xs of
    Nothing -> 0
    Just (index, slice) -> index + widthOf slice - offset

-- | A series of non-overlapping `Slice`s.
data Slices = Slices
  { segsOffset :: Int,
    segsElems :: IntMap Slice
  }
  -- slices indexed by their starting offsets
  deriving (Eq)

instance Show Slices where
  show (Slices offset xs) = "Slices " <> show offset <> " " <> show (IntMap.toList xs)

data RefUSlices
  = RefUSlices
      RefU -- the `RefU` this series of slices represents
      Slices -- slices indexed by their starting offsets
  deriving (Show, Eq)

--------------------------------------------------------------------------------

-- | Constructs a `Slice` with a `RefU` as its own parent
new :: RefU -> RefUSlices
new ref = RefUSlices ref (Slices 0 (IntMap.singleton 0 (Parent (widthOf ref))))

-- setConstant :: Slices -> Int -> U -> Slices
-- setConstant (Slices ref xs) index val = Slices ref $ IntMap.

-- | Given an interval [start, end), splits one `Slices` into three
-- split :: (Int, Int) -> Slices -> (Slices, Slices, Slices)
-- split (start, end) (Slices xs) =
--   let -- the smallest slice touched by the interval
--       smallestSlice = case IntMap.lookupLE start xs of
--         Nothing -> Nothing
--         Just (index, slice) -> -- divide this slice into two
--           Just (_, _)
splitSlice :: Int -> Slice -> (Slice, Slice)
splitSlice index slice = case slice of
  Constant val -> (Constant (U.slice val 0 index), Constant (U.slice val index (widthOf val - index)))
  ChildOf limb -> let (limb1, limb2) = Limb.split index limb in (ChildOf limb1, ChildOf limb2)
  Parent len -> (Parent index, Parent (len - index))

-- | Split a `Slices` into two at a given index
splitSlices :: Int -> Slices -> (Slices, Slices)
splitSlices index (Slices offset xs) = case IntMap.splitLookup index xs of
  (before, Just slice, after) -> (Slices offset before, Slices index (IntMap.insert index slice after))
  (before, Nothing, after) -> case IntMap.lookupLE index xs of
    Nothing -> (Slices offset mempty, Slices offset after)
    Just (index', slice) ->
      let (slice1, slice2) = splitSlice (index - index') slice
       in (Slices offset (IntMap.insert index' slice1 before), Slices index (IntMap.insert index slice2 after))

split :: Int -> RefUSlices -> (RefUSlices, RefUSlices)
split index (RefUSlices ref slices) =
  let (before, after) = splitSlices index slices
   in (RefUSlices ref before, RefUSlices ref after)


-- (Slices before, Slices after)

--       (middle', after') = IntMap.split end middle
--    in undefined

-- | Given an interval [start, end), returns `Slices` that are contained in the interval.
-- lookup :: (Int, Int) -> Slices -> Slices
-- lookup (start, end) (Slices xs) =

--   let a = 0
--       -- the smallest slice touched by the interval
--       smallestSlice = IntMap.lookupLE start xs
--   in Slices $ IntMap.filterWithKey (\k _ -> k >= start && k < end) xs
