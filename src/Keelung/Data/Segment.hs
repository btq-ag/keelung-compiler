module Keelung.Data.Segment (Segments (..), Segment (..), RefUSegments (..), new, split, splitSegments) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Keelung (HasWidth, widthOf)
import Keelung.Data.Limb (Limb)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference (RefU)
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U

--------------------------------------------------------------------------------

-- | A segment of a `RefU`
data Segment
  = Constant U
  | ChildOf Limb -- it's a child of another
  | Parent Int --  here stores the length of this Segment
  deriving (Eq)

instance Show Segment where
  show (Constant u) = "Constant[" <> show (widthOf u) <> "] " <> show u
  show (ChildOf limb) = "ChildOf[" <> show (widthOf limb) <> "] " <> show limb
  show (Parent len) = "Parent[" <> show len <> "]"

instance HasWidth Segment where
  widthOf (Constant u) = widthOf u
  widthOf (ChildOf limb) = widthOf limb
  widthOf (Parent len) = len

instance HasWidth Segments where
  widthOf (Segments offset xs) = case IntMap.lookupMax xs of
    Nothing -> 0
    Just (index, segment) -> index + widthOf segment - offset

-- | A series of non-overlapping `Segment`s.
data Segments = Segments
  { segsOffset :: Int,
    segsElems :: IntMap Segment
  }
  -- segments indexed by their starting offsets
  deriving (Eq)

instance Show Segments where
  show (Segments offset xs) = "Segments " <> show offset <> " " <> show (IntMap.toList xs)

data RefUSegments
  = RefUSegments
      RefU -- the `RefU` this series of segments represents
      Segments -- segments indexed by their starting offsets
  deriving (Show, Eq)

--------------------------------------------------------------------------------

-- | Constructs a `Segment` with a `RefU` as its own parent
new :: RefU -> RefUSegments
new ref = RefUSegments ref (Segments 0 (IntMap.singleton 0 (Parent (widthOf ref))))

-- setConstant :: Segments -> Int -> U -> Segments
-- setConstant (Segments ref xs) index val = Segments ref $ IntMap.

-- | Given an interval [start, end), splits one `Segments` into three
-- split :: (Int, Int) -> Segments -> (Segments, Segments, Segments)
-- split (start, end) (Segments xs) =
--   let -- the smallest segment touched by the interval
--       smallestSegment = case IntMap.lookupLE start xs of
--         Nothing -> Nothing
--         Just (index, segment) -> -- divide this segment into two
--           Just (_, _)
splitSegment :: Int -> Segment -> (Segment, Segment)
splitSegment index segment = case segment of
  Constant val -> (Constant (U.slice val 0 index), Constant (U.slice val index (widthOf val - index)))
  ChildOf limb -> let (limb1, limb2) = Limb.split index limb in (ChildOf limb1, ChildOf limb2)
  Parent len -> (Parent index, Parent (len - index))

-- | Split a `Segments` into two at a given index
splitSegments :: Int -> Segments -> (Segments, Segments)
splitSegments index (Segments offset xs) = case IntMap.splitLookup index xs of
  (before, Just segment, after) -> (Segments offset before, Segments index (IntMap.insert index segment after))
  (before, Nothing, after) -> case IntMap.lookupLE index xs of
    Nothing -> (Segments offset mempty, Segments offset after)
    Just (index', segment) ->
      let (segment1, segment2) = splitSegment (index - index') segment
       in (Segments offset (IntMap.insert index' segment1 before), Segments index (IntMap.insert index segment2 after))

split :: Int -> RefUSegments -> (RefUSegments, RefUSegments)
split index (RefUSegments ref segments) =
  let (before, after) = splitSegments index segments
   in (RefUSegments ref before, RefUSegments ref after)

-- (Segments before, Segments after)

--       (middle', after') = IntMap.split end middle
--    in undefined

-- | Given an interval [start, end), returns `Segments` that are contained in the interval.
-- lookup :: (Int, Int) -> Segments -> Segments
-- lookup (start, end) (Segments xs) =

--   let a = 0
--       -- the smallest segment touched by the interval
--       smallestSegment = IntMap.lookupLE start xs
--   in Segments $ IntMap.filterWithKey (\k _ -> k >= start && k < end) xs
