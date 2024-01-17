{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use list comprehension" #-}

-- | For representing results of looking up a "Slice" of a "RefU"
module Keelung.Data.SliceLookup
  ( -- * Construction
    Segment (..),
    nullSegment,
    sameKindOfSegment,
    SliceLookup (..),
    fromRefU,
    fromSegment,

    -- * Mapping
    map,
    mapInterval,
    mapIntervalWithSlice,
    pad,

    -- * Splitting and slicing
    splitSegment,
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

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Keelung (HasWidth, widthOf)
import Keelung.Data.Reference (RefU)
import Keelung.Data.Slice (Slice (..))
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Prelude hiding (map)

--------------------------------------------------------------------------------

-- | Either a constant value, or a part of an RefU, or a parent itself
data Segment
  = Constant U
  | ChildOf Slice -- part of some RefU
  | Parent
      Int -- length of this segment
      (Map RefU Slice) -- children
      (IntMap Slice) -- children of the same RefU
      (IntMap Slice) -- parents of the same RefU
  | Empty
      Int -- length of this segment
  deriving (Eq)

instance Show Segment where
  show (Constant u) = "Constant[" <> show (widthOf u) <> "] " <> show u
  show (ChildOf limb) = "ChildOf[" <> show (widthOf limb) <> "] " <> show limb
  show (Parent len children childSelfRefs parentSelfRefs) =
    "Parent["
      <> show len
      <> "] "
      <> show (Map.toList children)
      <> (if IntMap.null childSelfRefs then "" else " " <> show (IntMap.elems childSelfRefs))
      <> (if IntMap.null parentSelfRefs then "" else " " <> show (IntMap.elems parentSelfRefs))
  show (Empty len) = "Empty[" <> show len <> "]"

instance HasWidth Segment where
  widthOf (Constant u) = widthOf u
  widthOf (ChildOf limb) = widthOf limb
  widthOf (Parent len _ _ _) = len
  widthOf (Empty len) = len

-- | A "SliceLookup" of a RefU, with non-overlapping Segments indexed by their starting offset
data SliceLookup = SliceLookup
  { lookupSlice :: Slice, -- the Slice these segments belong to
    lookupSegments :: IntMap Segment -- the segments
  }
  deriving (Eq)

instance Show SliceLookup where
  show (SliceLookup slice xs) = "SliceLookup " <> show slice <> " " <> show (IntMap.toList xs)

instance HasWidth SliceLookup where
  widthOf (SliceLookup slice _) = widthOf slice

instance Semigroup SliceLookup where
  (<>) = merge

-- | Check if two Segments are of the same kind
sameKindOfSegment :: Segment -> Segment -> Bool
sameKindOfSegment (Constant _) (Constant _) = True
sameKindOfSegment (ChildOf _) (ChildOf _) = True
sameKindOfSegment (Empty _) (Empty _) = True
sameKindOfSegment (Parent {}) (Parent {}) = False
sameKindOfSegment _ _ = False

-- | Check if a `Segment` is empty
nullSegment :: Segment -> Bool
nullSegment (Constant val) = widthOf val == 0
nullSegment (ChildOf slice) = Slice.null slice
nullSegment (Parent len _ _ _) = len == 0
nullSegment (Empty len) = len == 0

-- | Check if a `Segment` is valid
validSegment :: Segment -> Bool
validSegment (Constant val) = widthOf val >= 0
validSegment (ChildOf _) = True
validSegment (Parent len children childSelfRefs parentSelfRefs) = len >= 0 && (not (Map.null children) || not (IntMap.null childSelfRefs) || not (IntMap.null parentSelfRefs))
validSegment (Empty len) = len >= 0

--------------------------------------------------------------------------------

-- | Constructs a `SliceLookup` with a `RefU` as its own parent
fromRefU :: RefU -> SliceLookup
fromRefU ref = SliceLookup (Slice ref 0 (widthOf ref)) (IntMap.singleton 0 (Empty (widthOf ref)))

-- | Constructs a `SliceLookup` from a `Segment` and its `Slice`
fromSegment :: Slice -> Segment -> SliceLookup
fromSegment (Slice ref start end) segment =
  let refUWidth = widthOf ref
      isEmpty = case segment of
        Empty _ -> True
        _ -> False
   in SliceLookup (Slice ref 0 refUWidth) $
        IntMap.fromList $
          if isEmpty
            then [(0, Empty refUWidth)]
            else
              if start > 0
                then
                  if refUWidth > end
                    then [(0, Empty start), (start, segment), (end, Empty (refUWidth - end))]
                    else [(0, Empty start), (start, segment)]
                else
                  if refUWidth > end
                    then [(0, segment), (end, Empty (refUWidth - end))]
                    else [(0, segment)]

-- | Split a `Segment` into two at a given index (relative to the starting offset of the Segement)
splitSegment :: Int -> Segment -> (Segment, Segment)
splitSegment index segment = case segment of
  Constant val -> (Constant (U.slice val 0 index), Constant (U.slice val index (widthOf val - index)))
  ChildOf slice -> let (slice1, slice2) = Slice.split index slice in (ChildOf slice1, ChildOf slice2)
  Parent len children childSelfRefs parentSelfRefs ->
    let splittedChildren = fmap (Slice.split index) children
        children1 = fmap fst splittedChildren
        children2 = fmap snd splittedChildren
        splittedChildSelfRefs = fmap (Slice.split index) childSelfRefs
        splittedParentSelfRefs = fmap (Slice.split index) parentSelfRefs
        childSelfRefs1 = fmap fst splittedChildSelfRefs
        childSelfRefs2 = fmap snd splittedChildSelfRefs
        parentSelfRefs1 = fmap fst splittedParentSelfRefs
        parentSelfRefs2 = fmap snd splittedParentSelfRefs
     in (Parent index children1 childSelfRefs1 parentSelfRefs1, Parent (len - index) children2 childSelfRefs2 parentSelfRefs2)
  Empty len -> (Empty index, Empty (len - index))

-- | Split a `SliceLookup` into two at a given index
split :: Int -> SliceLookup -> (SliceLookup, SliceLookup)
split index (SliceLookup (Slice ref start end) xs) = case IntMap.splitLookup index xs of
  (before, Just segment, after) -> (SliceLookup (Slice ref start index) before, SliceLookup (Slice ref index end) (IntMap.insert index segment after))
  (before, Nothing, after) -> case IntMap.lookupLE index xs of
    Nothing -> (SliceLookup (Slice ref start start) mempty, SliceLookup (Slice ref start end) after)
    Just (index', segment) ->
      let (segment1, segment2) = splitSegment (index - index') segment
       in (SliceLookup (Slice ref start index) (IntMap.insert index' segment1 before), SliceLookup (Slice ref index end) (IntMap.insert index segment2 after))

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
      then IntMap.insert 0 (Empty start) xs
      else xs

-- | Pad the ending end of a SliceLookup with empty Segment (Parent) so that the whole SliceLookup ends at the width of the RefU
padEnd :: SliceLookup -> SliceLookup
padEnd (SliceLookup (Slice ref start end) xs) =
  SliceLookup (Slice ref start (widthOf ref)) $
    if end < widthOf ref
      then IntMap.insert end (Empty (widthOf ref - end)) xs
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

-- | See if 2 Segments can be glued together
glueSegment :: Segment -> Segment -> Either Slice.MergeError (Maybe Segment)
glueSegment xs ys = case (xs, ys) of
  (Constant val1, Constant val2) -> Right (Just (Constant (val2 <> val1)))
  (ChildOf slice1, ChildOf slice2) -> case Slice.safeMerge slice1 slice2 of
    Left err -> Left err
    Right slice -> Right (Just (ChildOf slice))
  (Parent len1 children1 childSelfRefs1 parentSelfRefs1, Parent len2 children2 childSelfRefs2 parentSelfRefs2) ->
    -- ignoring all erred merges
    let childrenIntersection = snd $ Map.mapEither id $ Map.intersectionWith Slice.safeMerge children1 children2
        childSelfRefsIntersection = snd $ IntMap.mapEither id $ IntMap.intersectionWith Slice.safeMerge childSelfRefs1 childSelfRefs2
        parentSelfRefsIntersection = snd $ IntMap.mapEither id $ IntMap.intersectionWith Slice.safeMerge parentSelfRefs1 parentSelfRefs2
     in if len1 + len2 == 0
          || Map.size childrenIntersection /= Map.size children1
          || IntMap.size childSelfRefsIntersection /= IntMap.size childSelfRefs1
          || IntMap.size parentSelfRefsIntersection /= IntMap.size parentSelfRefs1
          then Right Nothing
          else Right (Just (Parent (len1 + len2) childrenIntersection childSelfRefsIntersection parentSelfRefsIntersection))
  (Empty len1, Empty len2) ->
    if len1 + len2 == 0
      then Right Nothing
      else Right (Just (Empty (len1 + len2)))
  _ ->
    if nullSegment xs
      then Right (Just ys)
      else
        if nullSegment ys
          then Right (Just xs)
          else Right Nothing

-- | Glue all segments that can be glued together, such that `normalize . merge` is the inverse of `split`
normalize :: SliceLookup -> SliceLookup
normalize (SliceLookup (Slice ref start end) xs) =
  let (accumulated, lastSliceLookup) = IntMap.foldlWithKey' glue (mempty, Nothing) xs
   in SliceLookup (Slice ref start end) $ case lastSliceLookup of
        Nothing -> accumulated
        Just (index, segment) -> IntMap.insert index segment accumulated
  where
    glue (acc, Nothing) index segment =
      if nullSegment segment
        then (acc, Nothing) -- drop null segments
        else (IntMap.insert index segment acc, Just (index, segment))
    glue (acc, Just (prevIndex, prevSliceLookup)) index segment = case glueSegment prevSliceLookup segment of
      Right (Just result) -> (acc, Just (prevIndex, result))
      _ -> (IntMap.insert prevIndex prevSliceLookup acc, Just (index, segment))

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
          let notNull = not (nullSegment currSegment)
              noGapAndAdjecent = case previous of
                Nothing -> True
                Just (prevIndex, prevSegment) -> prevIndex + widthOf prevSegment == currIndex
              notSameKind = case previous of
                Nothing -> True
                Just (_, prevSegment) -> not (sameKindOfSegment prevSegment currSegment)
           in (acc && validSegment currSegment && notNull && noGapAndAdjecent && notSameKind, Just (currIndex, currSegment))
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
                if validSegment currSegment
                  then []
                  else [FailureNotValidSegment x currSegment]
              isNull =
                if nullSegment currSegment
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
                  if sameKindOfSegment prevSegment currSegment
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
