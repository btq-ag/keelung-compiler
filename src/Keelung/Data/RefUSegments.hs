{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use list comprehension" #-}

-- | For representing Segments of a RefU
module Keelung.Data.RefUSegments
  ( -- * Construction
    RefUSegments (RefUSegments),
    formatRefUSegments,
    PartialRefUSegments (PartialRefUSegments),
    fromRefU,
    fromSegment,
    toPartial,

    -- * Projection
    toRefU,
    toIntMap,

    -- * Query
    lookupAt,

    -- * Modification
    mapInterval,

    -- * Splitting and slicing
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
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Keelung (HasWidth, widthOf)
import Keelung.Data.Reference (RefU)
import Keelung.Data.Segment (Segment)
import Keelung.Data.Segment qualified as Segment
import Keelung.Data.Slice (Slice (..))
import Keelung.Data.Slice qualified as Slice
import Keelung.Syntax (Width)
import Prelude hiding (map, null)
import Prelude qualified

--------------------------------------------------------------------------------

-- | A "RefUSegments" of a RefU, with non-overlapping Segments indexed by their starting offset
data RefUSegments = RefUSegments
  { rsRefU :: RefU, -- the Slice these segments belong to
    rsSegments :: IntMap Segment -- the segments
  }
  deriving (Eq, Generic)

instance NFData RefUSegments

instance Show RefUSegments where
  show = unlines . formatRefUSegments

-- | For printing RefUSegments
formatRefUSegments :: RefUSegments -> [String]
formatRefUSegments (RefUSegments ref segments) =
  IntMap.toList segments >>= \(start, segment) ->
    let leftHandSide = padEnd8 (showRefU start (widthOf segment)) <> " = "
     in case segment of -- showing only parents
          Segment.Constant value -> [leftHandSide <> show value]
          Segment.ChildOf _ -> []
          Segment.ParentOf _ children ->
            let childrenStrings = show <$> concatMap Set.toList (Map.elems children)
             in case childrenStrings of
                  [] -> []
                  (x : xs) -> leftHandSide <> x : List.map ("           " <>) xs
          _ -> []
  where
    padEnd8 :: String -> String
    padEnd8 x = if length x < 8 then x ++ replicate (8 - length x) ' ' else x

    showRefU :: Int -> Width -> String
    showRefU start 1 = show ref <> "[" <> show start <> "]" -- Slice = a single bit
    showRefU start width =
      if start == 0 && width == widthOf ref
        then show ref -- Slice = the whole ref
        else show ref <> "[" <> show start <> ":" <> show (start + width) <> "]"

instance HasWidth RefUSegments where
  widthOf (RefUSegments slice _) = widthOf slice

--------------------------------------------------------------------------------

data PartialRefUSegments = PartialRefUSegments Slice (IntMap Segment)
  deriving (Eq, Generic, Show)

instance HasWidth PartialRefUSegments where
  widthOf (PartialRefUSegments slice _) = widthOf slice

toPartial :: RefUSegments -> PartialRefUSegments
toPartial (RefUSegments ref segments) = PartialRefUSegments (Slice ref 0 (widthOf ref)) segments

--------------------------------------------------------------------------------

-- | Constructs a `RefUSegments` with a `RefU` as its own parent
fromRefU :: RefU -> RefUSegments
fromRefU ref = RefUSegments ref (IntMap.singleton 0 (Segment.Free (widthOf ref)))

-- | Constructs a `RefUSegments` from a `Segment` and its `Slice`
fromSegment :: Slice -> Segment -> RefUSegments
fromSegment (Slice ref start end) segment =
  let refUWidth = widthOf ref
      isEmpty = case segment of
        Segment.Free _ -> True
        _ -> False
   in RefUSegments ref $
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

-- | Split a `RefUSegments` into two at a given absolute index
split :: Int -> IntMap Segment -> (IntMap Segment, IntMap Segment)
split index xs = case IntMap.splitLookup index xs of
  (before, Just segment, after) -> (before, IntMap.insert index segment after)
  (before, Nothing, after) -> case IntMap.lookupLE index xs of
    Nothing -> (mempty, after)
    Just (index', segment) ->
      let (segment1, segment2) = Segment.unsafeSplit (index - index') segment
       in case (Segment.null segment1, Segment.null segment2) of
            (True, True) ->
              -- xs = before <index> after
              (before, after)
            (True, False) ->
              -- index = index'
              -- xs = before <index> segment2 <> after
              (before, IntMap.insert index segment2 after)
            (False, True) ->
              -- xs = before <index'> segment1 <index> after
              (IntMap.insert index' segment1 before, after)
            (False, False) ->
              -- xs = before <index'> segment1 <index> segment2 <> after
              (IntMap.insert index' segment1 before, IntMap.insert index segment2 after)

-- | Given an interval, get a slice of RefUSegments
splice :: (Int, Int) -> RefUSegments -> PartialRefUSegments
splice (start, end) (RefUSegments ref segments) = case split start segments of
  (_, afterStart) -> case split end afterStart of
    (mid, _) -> PartialRefUSegments (Slice ref start end) mid

-- | Convert a `RefUSegments` to a IntMap of `Segment`s
toIntMap :: RefUSegments -> IntMap Segment
toIntMap = rsSegments

-- | Extract the `RefU` from a `RefUSegments`
toRefU :: RefUSegments -> RefU
toRefU = rsRefU

--------------------------------------------------------------------------------

-- | Lookup the value at a given index
lookupAt :: Int -> RefUSegments -> Maybe (Either (RefU, Int) Bool)
lookupAt index (RefUSegments _ xs) = do
  (start, segment) <- IntMap.lookupLE index xs
  case segment of
    Segment.Constant val -> Just $ Right (Bits.testBit val (index - start))
    Segment.ChildOf slice -> Just $ Left (Slice.sliceRefU slice, Slice.sliceStart slice + index - start)
    Segment.ParentOf _ _ -> Nothing
    Segment.Free _ -> Nothing

--------------------------------------------------------------------------------

-- | Given an interval, replace all segments with a single segment
mapInterval :: (Segment -> Segment) -> (Int, Int) -> RefUSegments -> RefUSegments
mapInterval f (start, end) (RefUSegments ref segments) = case split start segments of
  (beforeStart, afterStart) -> case split end afterStart of
    (middle, afterEnd) -> RefUSegments ref $ beforeStart <> fmap f middle <> afterEnd

--------------------------------------------------------------------------------

-- | Glue all segments that can be glued together, such that `normalize . merge` is the inverse of `split`
normalize :: RefUSegments -> RefUSegments
normalize (RefUSegments ref xs) =
  let (accumulated, lastRefUSegments) = IntMap.foldlWithKey' glue (mempty, Nothing) xs
   in RefUSegments ref $ case lastRefUSegments of
        Nothing -> accumulated
        Just (index, segment) -> IntMap.insert index segment accumulated
  where
    glue (acc, Nothing) index segment =
      if Segment.null segment
        then (acc, Nothing) -- drop null segments
        else (IntMap.insert index segment acc, Just (index, segment))
    glue (acc, Just (prevIndex, prevRefUSegments)) index segment = case Segment.tryMerge prevRefUSegments segment of
      Just result -> (acc, Just (prevIndex, result))
      Nothing -> (IntMap.insert prevIndex prevRefUSegments acc, Just (index, segment))

--------------------------------------------------------------------------------

-- | A RefUSegments is considered valid if:
--    1. all segments are non-null
--    2. all segments are valid
--    3. all segments are adjacent but not overlapping
--    4. all adjacent segments are not of the same kind
--    5. the whole RefU is covered by the segments
isValid :: RefUSegments -> Bool
isValid = Prelude.null . validate

data Error
  = NullSegment RefUSegments Segment
  | HasGapOrNotAdjacent RefUSegments Segment Segment
  | OfSameKindOfSegment RefUSegments Segment Segment
  | NotValidSegment RefUSegments Segment
  | NotCoveringAll RefUSegments
  deriving (Eq, Show)

validate :: RefUSegments -> [Error]
validate x@(RefUSegments ref xs) =
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
