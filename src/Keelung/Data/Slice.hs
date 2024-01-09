module Keelung.Data.Slice
  ( -- * Construction
    Segment (..),
    nullSegment,
    Slice (..),
    fromRefU,
    isValid,

    -- * Mapping
    map,
    mapInterval,

    -- * Splitting and slicing
    splitSegment,
    split,
    slice,

    -- * Normalizing
    normalize,

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
import Prelude hiding (map)

--------------------------------------------------------------------------------

-- | Either a constant value, or a part of an RefU, or a parent itself
data Segment
  = Constant U
  | ChildOf Limb -- part of some RefU
  | Parent Int -- parent itself (with a given length)
  deriving (Eq)

instance Show Segment where
  show (Constant u) = "Constant[" <> show (widthOf u) <> "] " <> show u
  show (ChildOf limb) = "ChildOf[" <> show (widthOf limb) <> "] " <> show limb
  show (Parent len) = "Parent[" <> show len <> "]"

instance HasWidth Segment where
  widthOf (Constant u) = widthOf u
  widthOf (ChildOf limb) = widthOf limb
  widthOf (Parent len) = len

-- | A "Slice" of a RefU, with non-overlapping Segments indexed by their starting offset
data Slice = Slice
  { sliceRefU :: RefU, -- the `RefU` this series of segments belongs to
    sliceOffset :: Int, -- the starting offset of the first segment
    sliceSegments :: IntMap Segment -- the segments
  }
  deriving (Eq)

instance Show Slice where
  show (Slice ref offset xs) = "Slice " <> show ref <> " " <> show offset <> " " <> show (IntMap.toList xs)

instance HasWidth Slice where
  widthOf (Slice _ offset xs) = case IntMap.lookupMax xs of
    Nothing -> 0
    Just (index, segment) -> index + widthOf segment - offset

instance Semigroup Slice where
  (<>) = merge

--------------------------------------------------------------------------------

-- | Constructs a `Slice` with a `RefU` as its own parent
fromRefU :: RefU -> Slice
fromRefU ref = Slice ref 0 (IntMap.singleton 0 (Parent (widthOf ref)))

-- | Split a `Segment` into two at a given index
splitSegment :: Int -> Segment -> (Segment, Segment)
splitSegment index segment = case segment of
  Constant val -> (Constant (U.slice val 0 index), Constant (U.slice val index (widthOf val - index)))
  ChildOf limb -> let (limb1, limb2) = Limb.split index limb in (ChildOf limb1, ChildOf limb2)
  Parent len -> (Parent index, Parent (len - index))

-- | Check if a `Segment` is empty
nullSegment :: Segment -> Bool
nullSegment (Constant val) = widthOf val == 0
nullSegment (ChildOf limb) = Limb.null limb
nullSegment (Parent len) = len == 0

-- | Split a `Slice` into two at a given index
split :: Int -> Slice -> (Slice, Slice)
split index (Slice ref offset xs) = case IntMap.splitLookup index xs of
  (before, Just segment, after) -> (Slice ref offset before, Slice ref index (IntMap.insert index segment after))
  (before, Nothing, after) -> case IntMap.lookupLE index xs of
    Nothing -> (Slice ref offset mempty, Slice ref offset after)
    Just (index', segment) ->
      let (segment1, segment12) = splitSegment (index - index') segment
       in (Slice ref offset (IntMap.insert index' segment1 before), Slice ref index (IntMap.insert index segment12 after))

-- | Given an interval, get a slice of Slice
slice :: (Int, Int) -> Slice -> Slice
slice (start, end) slices = case split start slices of
  (_, afterStart) -> case split end afterStart of
    (mid, _) -> mid

--------------------------------------------------------------------------------

-- | Map a function over all Segments
map :: (Segment -> Segment) -> Slice -> Slice
map f (Slice ref offset xs) = Slice ref offset (IntMap.map f xs)

-- | Map a function over a given interval of Slice
mapInterval :: (Segment -> Segment) -> (Int, Int) -> Slice -> Slice
mapInterval f (start, end) slices = case split start slices of
  (beforeStart, afterStart) -> case split end afterStart of
    (middle, afterEnd) -> beforeStart <> map f middle <> afterEnd

--------------------------------------------------------------------------------

-- | Merging two Slice
data MergeError
  = NotSameRefU Slice Slice -- two `Slice` are not of the same `RefU`
  | NotAdjacent Slice Slice -- two `Slice` are not adjacent
  | Overlapping Slice Slice -- two `Slice` are overlapping
  | CannotMergeLimbs
  deriving (Eq)

instance Show MergeError where
  show (NotSameRefU a b) = "Slice.MergeError: two slices are not of the same RefU:\n" <> show a <> "\n" <> show b
  show (NotAdjacent a b) = "Slice.MergeError: two slices are not adjacent with each other:\n" <> show a <> "\n" <> show b
  show (Overlapping a b) = "Slice.MergeError: two slices are overlapping with each other:\n" <> show a <> "\n" <> show b
  show CannotMergeLimbs = "Slice.MergeError: cannot merge two Limbs together"

-- | Merge two `Slice` into one, throwing MergeError if the slices are:
--    1. not of the same `RefU`
--    2. not adjacent
--    3. overlapping
safeMerge :: Slice -> Slice -> Either MergeError Slice
safeMerge slice1@(Slice ref1 offset1 xs1) slice2@(Slice ref2 offset2 xs2)
  | ref1 /= ref2 = Left (NotSameRefU slice1 slice2)
  | otherwise = case (offset1 + widthOf slice1) `compare` offset2 of
      LT -> Left (NotAdjacent slice1 slice2)
      GT -> Left (Overlapping slice1 slice2)
      EQ -> Right (Slice ref1 offset1 (xs1 <> xs2))

-- | Unsafe version of `safeMerge`
merge :: Slice -> Slice -> Slice
merge xs ys = case safeMerge xs ys of
  Left err -> error $ "[ panic ] " <> show err
  Right result -> result

-- | See if 2 Segments can be glued together
glueSegment :: Segment -> Segment -> Either Limb.MergeError (Maybe Segment)
glueSegment xs ys = case (xs, ys) of
  (Constant val1, Constant val2) -> Right (Just (Constant (val2 <> val1)))
  (ChildOf limb, ChildOf limb') -> case Limb.safeMerge limb limb' of
    Left err -> Left err
    Right limb'' -> Right (Just (ChildOf limb''))
  (Parent len, Parent len') -> Right (Just (Parent (len + len')))
  _ ->
    if nullSegment xs
      then Right (Just ys)
      else
        if nullSegment ys
          then Right (Just xs)
          else Right Nothing

-- | Glue all segments that can be glued together, such that `normalize . merge` is the inverse of `split`
normalize :: Slice -> Slice
normalize (Slice ref offset xs) =
  let (accumulated, lastSlice) = IntMap.foldlWithKey' glue (mempty, Nothing) xs
   in Slice ref offset $ case lastSlice of
        Nothing -> accumulated
        Just (index, segment) -> IntMap.insert index segment accumulated
  where
    glue (acc, Nothing) index segment =
      if nullSegment segment
        then (acc, Nothing) -- drop null segments
        else (IntMap.insert index segment acc, Just (index, segment))
    glue (acc, Just (prevIndex, prevSlice)) index segment = case glueSegment prevSlice segment of
      Right (Just result) -> (acc, Just (prevIndex, result))
      _ -> (IntMap.insert prevIndex prevSlice acc, Just (index, segment))

--------------------------------------------------------------------------------

-- | A Slice is considered valid if:
--    1. all segments are non-null
--    3. all segments are adjacent but not overlapping
--    4. all adjacent segments are not of the same kind
isValid :: Slice -> Bool
isValid (Slice _ _ xs) =
  fst $
    IntMap.foldlWithKey'
      ( \(acc, previous) currIndex currSegment ->
          let notNull = not (nullSegment currSegment)
              noGapAndAdjecent = case previous of
                Nothing -> True
                Just (prevIndex, prevSegment) -> prevIndex + widthOf prevSegment == currIndex
              notSameKind = case previous of
                Nothing -> True
                Just (_, prevSegment) -> not (sameKind (prevSegment, currSegment))
           in (acc && notNull && noGapAndAdjecent && notSameKind, Just (currIndex, currSegment))
      )
      (True, Nothing)
      xs
  where
    sameKind :: (Segment, Segment) -> Bool
    sameKind (Constant _, Constant _) = True
    sameKind (ChildOf _, ChildOf _) = True
    sameKind (Parent _, Parent _) = True
    sameKind _ = False
