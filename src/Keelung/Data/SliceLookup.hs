{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use list comprehension" #-}

-- | For representing results of looking up a "Slice" of a "RefU"
module Keelung.Data.SliceLookup
  ( -- * Construction
    SliceLookup (..),
    fromRefU,
    fromSegment,

    -- * Query
    lookupAt,

    -- * Modification
    mapInterval,

    -- * Splitting and slicing
    split,
    splice,

    -- * Normalizing
    normalize,

    -- * Testing
    Error (..),
    isValid,
    validate,
  )
where

import Control.DeepSeq (NFData)
import Data.Bits qualified as Bits
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
import Prelude qualified

--------------------------------------------------------------------------------

-- | A "SliceLookup" of a RefU, with non-overlapping Segments indexed by their starting offset
data SliceLookup = SliceLookup
  { lookupRefU :: RefU, -- the Slice these segments belong to
    lookupSegments :: IntMap Segment -- the segments
  }
  deriving (Eq, Generic)

instance NFData SliceLookup

instance Show SliceLookup where
  show (SliceLookup ref segments) = show ref <> ": " <> show (IntMap.elems segments)

instance HasWidth SliceLookup where
  widthOf (SliceLookup slice _) = widthOf slice

--------------------------------------------------------------------------------

-- | Constructs a `SliceLookup` with a `RefU` as its own parent
fromRefU :: RefU -> SliceLookup
fromRefU ref = SliceLookup ref (IntMap.singleton 0 (Segment.Free (widthOf ref)))

-- | Constructs a `SliceLookup` from a `Segment` and its `Slice`
fromSegment :: Slice -> Segment -> SliceLookup
fromSegment (Slice ref start end) segment =
  let refUWidth = widthOf ref
      isEmpty = case segment of
        Segment.Free _ -> True
        _ -> False
   in SliceLookup ref $
        IntMap.fromList $
          if isEmpty
            then [(0, Segment.Free refUWidth)]
            else
              if start > 0
                then
                  if refUWidth > end
                    then [(0, Segment.Free start), (start, segment), (end, Segment.Free (refUWidth - end))]
                    else [(0, Segment.Free start), (start, segment)]
                else
                  if refUWidth > end
                    then [(0, segment), (end, Segment.Free (refUWidth - end))]
                    else [(0, segment)]

-- | Split a `SliceLookup` into two at a given absolute index
split :: Int -> SliceLookup -> (RefU, IntMap Segment, IntMap Segment)
split index (SliceLookup ref xs) = case IntMap.splitLookup index xs of
  (before, Just segment, after) -> (ref, before, IntMap.insert index segment after)
  (before, Nothing, after) -> case IntMap.lookupLE index xs of
    Nothing -> (ref, mempty, after)
    Just (index', segment) ->
      let (segment1, segment2) = Segment.unsafeSplit (index - index') segment
       in case (Segment.null segment1, Segment.null segment2) of
            (True, True) ->
              -- xs = before <index> after
              (ref, before, after)
            (True, False) ->
              -- index = index'
              -- xs = before <index> segment2 <> after
              (ref, before, IntMap.insert index segment2 after)
            (False, True) ->
              -- xs = before <index'> segment1 <index> after
              (ref, IntMap.insert index' segment1 before, after)
            (False, False) ->
              -- xs = before <index'> segment1 <index> segment2 <> after
              (ref, IntMap.insert index' segment1 before, IntMap.insert index segment2 after)

-- | Given an interval, get a slice of SliceLookup
splice :: (Int, Int) -> SliceLookup -> SliceLookup
splice (start, end) lookups = case split start lookups of
  (ref, _, afterStart) -> case split end (SliceLookup ref afterStart) of
    (_, mid, _) -> SliceLookup ref mid

--------------------------------------------------------------------------------

-- | Lookup the value at a given index
lookupAt :: Int -> SliceLookup -> Maybe (Either (RefU, Int) Bool)
lookupAt index (SliceLookup _ xs) = do
  (start, segment) <- IntMap.lookupLE index xs
  case segment of
    Segment.Constant val -> Just $ Right (Bits.testBit val (index - start))
    Segment.ChildOf slice -> Just $ Left (Slice.sliceRefU slice, Slice.sliceStart slice + index - start)
    Segment.Parent _ _ -> Nothing
    Segment.Free _ -> Nothing

--------------------------------------------------------------------------------

-- | Given an interval, replace all segments with a single segment
mapInterval :: (Segment -> Segment) -> (Int, Int) -> SliceLookup -> SliceLookup
mapInterval f (start, end) lookups = case split start lookups of
  (ref, beforeStart, afterStart) -> case split end (SliceLookup ref afterStart) of
    (_, middle, afterEnd) -> SliceLookup ref $ beforeStart <> fmap f middle <> afterEnd

--------------------------------------------------------------------------------

-- | Glue all segments that can be glued together, such that `normalize . merge` is the inverse of `split`
normalize :: SliceLookup -> SliceLookup
normalize (SliceLookup ref xs) =
  let (accumulated, lastSliceLookup) = IntMap.foldlWithKey' glue (mempty, Nothing) xs
   in SliceLookup ref $ case lastSliceLookup of
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
--    2. all segments are valid
--    3. all segments are adjacent but not overlapping
--    4. all adjacent segments are not of the same kind
--    5. the whole RefU is covered by the segments
isValid :: SliceLookup -> Bool
isValid = Prelude.null . validate

data Error
  = NullSegment SliceLookup Segment
  | HasGapOrNotAdjacent SliceLookup Segment Segment
  | OfSameKindOfSegment SliceLookup Segment Segment
  | NotValidSegment SliceLookup Segment
  | NotCoveringAll SliceLookup
  deriving (Eq, Show)

validate :: SliceLookup -> [Error]
validate x@(SliceLookup ref xs) =
  let (errors, finalState) =
        IntMap.foldlWithKey'
          ( \(acc, previous) currIndex currSegment ->
              let isValidSegment =
                    if Segment.isValid currSegment
                      then []
                      else [NotValidSegment x currSegment]
                  isNull =
                    if Segment.null currSegment
                      then [NullSegment x currSegment]
                      else []
                  hasGapOrNotAdjacent = case previous of
                    Nothing -> []
                    Just (prevIndex, prevSegment) ->
                      if prevIndex + widthOf prevSegment == currIndex
                        then []
                        else [HasGapOrNotAdjacent x prevSegment currSegment]
                  notSameKind = case previous of
                    Nothing -> []
                    Just (_, prevSegment) ->
                      if Segment.sameKind prevSegment currSegment
                        then [OfSameKindOfSegment x prevSegment currSegment]
                        else []
                  coveringAll = case previous of
                    Nothing -> if currIndex == 0 then [] else [NotCoveringAll x]
                    _ -> []
               in ( acc
                      <> isValidSegment
                      <> isNull
                      <> hasGapOrNotAdjacent
                      <> notSameKind
                      <> coveringAll,
                    Just (currIndex, currSegment)
                  )
          )
          ([], Nothing)
          xs
   in case finalState of
        Nothing -> []
        Just (lastIndex, lastSegment) -> if lastIndex + widthOf lastSegment == widthOf ref then errors else NotCoveringAll x : errors
