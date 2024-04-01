{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use list comprehension" #-}

-- | For representing results of looking up a "Slice" of a "RefU"
module Keelung.Data.SliceLookup
  ( -- * Construction
    SliceLookup (..),
    fromRefU,
    fromSegment,
    null,

    -- * Mapping
    map,
    mapInterval,
    mapIntervalWithSlice,
    pad,

    -- * Splitting and slicing
    split,
    splice,

    -- * Normalizing
    normalize,

    -- * Merging
    MergeError (..),
    merge,
    safeMerge,

    -- * Testing
    Failure (..),
    isValid,
    collectFailure,
  )
where

import Control.DeepSeq (NFData)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import GHC.Generics (Generic)
import Keelung (HasWidth, widthOf)
import Keelung.Data.Reference (RefU)
import Keelung.Data.Segment (Segment)
import Keelung.Data.Segment qualified as Segment
import Keelung.Data.Slice (Slice (..))
import Keelung.Data.Slice qualified as Slice
import Prelude hiding (map, null)

--------------------------------------------------------------------------------

-- | A "SliceLookup" of a RefU, with non-overlapping Segments indexed by their starting offset
data SliceLookup = SliceLookup
  { lookupSlice :: Slice, -- the Slice these segments belong to
    lookupSegments :: IntMap Segment -- the segments
  }
  deriving (Eq, Generic)

instance NFData SliceLookup

instance Show SliceLookup where
  show (SliceLookup slice segments) = show (sliceRefU slice) <> " " <> show (sliceStart slice) <> " ... " <> show (sliceEnd slice) <> ": " <> show (IntMap.elems segments)

instance HasWidth SliceLookup where
  widthOf (SliceLookup slice _) = widthOf slice

instance Semigroup SliceLookup where
  (<>) = merge

-- | See if a `SliceLookup` is empty
null :: SliceLookup -> Bool
null (SliceLookup slice _) = Slice.null slice

--------------------------------------------------------------------------------

-- | Constructs a `SliceLookup` with a `RefU` as its own parent
fromRefU :: RefU -> SliceLookup
fromRefU ref = SliceLookup (Slice ref 0 (widthOf ref)) (IntMap.singleton 0 (Segment.Empty (widthOf ref)))

-- | Constructs a `SliceLookup` from a `Segment` and its `Slice`
fromSegment :: Slice -> Segment -> SliceLookup
fromSegment (Slice ref start end) segment =
  let refUWidth = widthOf ref
      isEmpty = case segment of
        Segment.Empty _ -> True
        _ -> False
   in SliceLookup (Slice ref 0 refUWidth) $
        IntMap.fromList $
          if isEmpty
            then [(0, Segment.Empty refUWidth)]
            else
              if start > 0
                then
                  if refUWidth > end
                    then [(0, Segment.Empty start), (start, segment), (end, Segment.Empty (refUWidth - end))]
                    else [(0, Segment.Empty start), (start, segment)]
                else
                  if refUWidth > end
                    then [(0, segment), (end, Segment.Empty (refUWidth - end))]
                    else [(0, segment)]

-- | Split a `SliceLookup` into two at a given absolute index
split :: Int -> SliceLookup -> (SliceLookup, SliceLookup)
split index (SliceLookup (Slice ref start end) xs) = case IntMap.splitLookup index xs of
  (before, Just segment, after) -> (SliceLookup (Slice ref start index) before, SliceLookup (Slice ref index end) (IntMap.insert index segment after))
  (before, Nothing, after) -> case IntMap.lookupLE index xs of
    Nothing -> (SliceLookup (Slice ref start start) mempty, SliceLookup (Slice ref start end) after)
    Just (index', segment) ->
      let (segment1, segment2) = Segment.unsafeSplit (index - index') segment
       in case (Segment.null segment1, Segment.null segment2) of
            (True, True) ->
              -- xs = before <index> after
              ( SliceLookup (Slice ref start index) before,
                SliceLookup (Slice ref index end) after
              )
            (True, False) ->
              -- index = index'
              -- xs = before <index> segment2 <> after
              ( SliceLookup (Slice ref start index) before,
                SliceLookup (Slice ref index end) (IntMap.insert index segment2 after)
              )
            (False, True) ->
              -- xs = before <index'> segment1 <index> after
              ( SliceLookup (Slice ref start index) (IntMap.insert index' segment1 before),
                SliceLookup (Slice ref index end) after
              )
            (False, False) ->
              -- xs = before <index'> segment1 <index> segment2 <> after
              ( SliceLookup (Slice ref start index) (IntMap.insert index' segment1 before),
                SliceLookup (Slice ref index end) (IntMap.insert index segment2 after)
              )

-- | Given an interval, get a slice of SliceLookup
splice :: (Int, Int) -> SliceLookup -> SliceLookup
splice (start, end) lookups = case split start lookups of
  (_, afterStart) -> case split end afterStart of
    (mid, _) -> mid

--------------------------------------------------------------------------------

-- | Map a function over all Segments
map :: (Segment -> Segment) -> SliceLookup -> SliceLookup
map f (SliceLookup slice xs) = SliceLookup slice (IntMap.map f xs)

mapWithSlice :: (Slice -> Segment -> Segment) -> SliceLookup -> SliceLookup
mapWithSlice f (SliceLookup (Slice ref start end) xs) = SliceLookup (Slice ref start end) (IntMap.mapWithKey (\index segment -> f (Slice ref index (widthOf segment)) segment) xs)

-- | Map a function over a given interval of SliceLookup
mapInterval :: (Segment -> Segment) -> (Int, Int) -> SliceLookup -> SliceLookup
mapInterval f (start, end) lookups = case split start lookups of
  (beforeStart, afterStart) -> case split end afterStart of
    (middle, afterEnd) -> beforeStart <> map f middle <> afterEnd

-- | Map a function over a given interval of SliceLookup
mapIntervalWithSlice :: (Slice -> Segment -> Segment) -> Slice -> SliceLookup -> SliceLookup
mapIntervalWithSlice f (Slice _ start end) lookups = case split start lookups of
  (beforeStart, afterStart) -> case split end afterStart of
    (middle, afterEnd) -> beforeStart <> mapWithSlice f middle <> afterEnd

--------------------------------------------------------------------------------

-- | Pad both ends of a SliceLookup with empty Segments (Parent) so that it covers the whole RefU
pad :: SliceLookup -> SliceLookup
pad = padStart . padEnd

-- | Pad the starting end of a SliceLookup with empty Segment (Parent) so that the whole SliceLookup starts from 0
padStart :: SliceLookup -> SliceLookup
padStart (SliceLookup (Slice ref start end) xs) =
  SliceLookup (Slice ref 0 end) $
    if start > 0
      then IntMap.insert 0 (Segment.Empty start) xs
      else xs

-- | Pad the ending end of a SliceLookup with empty Segment (Parent) so that the whole SliceLookup ends at the width of the RefU
padEnd :: SliceLookup -> SliceLookup
padEnd (SliceLookup (Slice ref start end) xs) =
  SliceLookup (Slice ref start (widthOf ref)) $
    if end < widthOf ref
      then IntMap.insert end (Segment.Empty (widthOf ref - end)) xs
      else xs

--------------------------------------------------------------------------------

-- | Merging two SliceLookup
data MergeError
  = NotSameRefU SliceLookup SliceLookup -- two `SliceLookup` are not of the same `RefU`
  | NotAdjacent SliceLookup SliceLookup -- two `SliceLookup` are not adjacent
  | Overlapping SliceLookup SliceLookup -- two `SliceLookup` are overlapping
  deriving (Eq)

instance Show MergeError where
  show (NotSameRefU a b) = "SliceLookup.MergeError: two lookups are not of the same RefU:\n" <> show a <> "\n" <> show b
  show (NotAdjacent a b) = "SliceLookup.MergeError: two lookups are not adjacent with each other:\n" <> show a <> "\n" <> show b
  show (Overlapping a b) = "SliceLookup.MergeError: two lookups are overlapping with each other:\n" <> show a <> "\n" <> show b

-- | Merge two `SliceLookup` into one, throwing MergeError if the lookups are:
--    1. not of the same `RefU`
--    2. not adjacent
--    3. overlapping
safeMerge :: SliceLookup -> SliceLookup -> Either MergeError SliceLookup
safeMerge lookup1@(SliceLookup (Slice ref1 start1 end1) xs1) lookup2@(SliceLookup (Slice ref2 start2 end2) xs2)
  | ref1 /= ref2 = Left (NotSameRefU lookup1 lookup2)
  | otherwise = case end1 `compare` start2 of
      LT -> Left (NotAdjacent lookup1 lookup2)
      GT -> Left (Overlapping lookup1 lookup2)
      EQ -> Right (SliceLookup (Slice ref1 start1 end2) (xs1 <> xs2))

-- | Unsafe version of `safeMerge`
merge :: SliceLookup -> SliceLookup -> SliceLookup
merge xs ys = case safeMerge xs ys of
  Left err -> error $ "[ panic ] " <> show err
  Right result -> result

-- | Glue all segments that can be glued together, such that `normalize . merge` is the inverse of `split`
normalize :: SliceLookup -> SliceLookup
normalize (SliceLookup (Slice ref start end) xs) =
  let (accumulated, lastSliceLookup) = IntMap.foldlWithKey' glue (mempty, Nothing) xs
   in SliceLookup (Slice ref start end) $ case lastSliceLookup of
        Nothing -> accumulated
        Just (index, segment) -> IntMap.insert index segment accumulated
  where
    glue (acc, Nothing) index segment =
      if Segment.null segment
        then (acc, Nothing) -- drop null segments
        else (IntMap.insert index segment acc, Just (index, segment))
    glue (acc, Just (prevIndex, prevSliceLookup)) index segment = case Segment.tryMerge prevSliceLookup segment of
      Just result -> (acc, Just (prevIndex, result))
      Nothing -> (IntMap.insert prevIndex prevSliceLookup acc, Just (index, segment))

--------------------------------------------------------------------------------

-- | A SliceLookup is considered valid if:
--    1. all segments are non-null
--    3. all segments are adjacent but not overlapping
--    4. all adjacent segments are not of the same kind
isValid :: SliceLookup -> Bool
isValid (SliceLookup _ xs) =
  fst $
    IntMap.foldlWithKey'
      ( \(acc, previous) currIndex currSegment ->
          let notNull = not (Segment.null currSegment)
              noGapAndAdjecent = case previous of
                Nothing -> True
                Just (prevIndex, prevSegment) -> prevIndex + widthOf prevSegment == currIndex
              notSameKind = case previous of
                Nothing -> True
                Just (_, prevSegment) -> not (Segment.sameKind prevSegment currSegment)
           in (acc && Segment.isValid currSegment && notNull && noGapAndAdjecent && notSameKind, Just (currIndex, currSegment))
      )
      (True, Nothing)
      xs

data Failure
  = FailureNullSegment SliceLookup Segment
  | FailureHasGapOrNotAdjacent SliceLookup Segment Segment
  | FailureOfSameKindOfSegment SliceLookup Segment Segment
  | FailureNotValidSegment SliceLookup Segment
  deriving (Eq, Show)

collectFailure :: Bool -> SliceLookup -> [Failure]
collectFailure checkSameKindOfSegment x@(SliceLookup _ xs) =
  fst $
    IntMap.foldlWithKey'
      ( \(acc, previous) currIndex currSegment ->
          let isValidSegment =
                if Segment.isValid currSegment
                  then []
                  else [FailureNotValidSegment x currSegment]
              isNull =
                if Segment.null currSegment
                  then [FailureNullSegment x currSegment]
                  else []
              hasGapOrNotAdjacent = case previous of
                Nothing -> []
                Just (prevIndex, prevSegment) ->
                  if prevIndex + widthOf prevSegment == currIndex
                    then []
                    else [FailureHasGapOrNotAdjacent x prevSegment currSegment]
              notSameKind = case previous of
                Nothing -> []
                Just (_, prevSegment) ->
                  if Segment.sameKind prevSegment currSegment
                    then [FailureOfSameKindOfSegment x prevSegment currSegment]
                    else []
           in ( isValidSegment
                  <> isNull
                  <> hasGapOrNotAdjacent
                  <> (if checkSameKindOfSegment then notSameKind else [])
                  <> acc,
                Just (currIndex, currSegment)
              )
      )
      ([], Nothing)
      xs
