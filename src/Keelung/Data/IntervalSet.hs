{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use guards" #-}

module Keelung.Data.IntervalSet
  ( -- * Construction
    IntervalSet (unIntervalSet),
    Case (..),
    new,
    singleton,

    -- * Operations
    normalize,
    insert,
    split,
    merge,
    multiplyBy,

    -- * Conversion
    toIntervalTable,

    -- * Query
    intervalsWithin,
    totalCount,
    getStartOffset,
    null,
    lookup,
    member,
    Error (..),
    validate,
    isValid,
  )
where

import Control.DeepSeq (NFData)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List qualified as List
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import GHC.Generics (Generic)
import Keelung.Compiler.Util (showList')
import Keelung.Data.IntervalTable (IntervalTable (IntervalTable))
import Prelude hiding (lookup, null)

-- | Key: start of an interval
--   Value: (end of the interval, count of the interval)
--    invariant: no two intervals overlap
newtype IntervalSet n = IntervalSet {unIntervalSet :: IntMap (Int, n)} deriving (Eq, Ord, Functor, Generic)

instance (Eq n, Num n, Show n) => Show (IntervalSet n) where
  show (IntervalSet xs) =
    showList'
      $ map
        ( \(start, (end, count)) ->
            if end - start == 1 && count /= 0
              then (if count == 1 then "" else show count) <> "$" <> show start
              else
                ( if count == 1
                    then "$" <> show start <> " ~ $" <> show (end - 1)
                    else show count <> "($" <> show start <> " ~ $" <> show (end - 1) <> ")"
                )
        )
      $ IntMap.toList xs

instance (NFData n) => NFData (IntervalSet n)

instance (Num n, Eq n) => Semigroup (IntervalSet n) where
  (<>) = merge

instance (Num n, Eq n) => Monoid (IntervalSet n) where
  mempty = new

type Interval = (Int, Int) -- (start, end)

--------------------------------------------------------------------------------

-- | O(1): Create an empty interval set
new :: IntervalSet n
new = IntervalSet mempty

-- | O(1): Create a 1-length interval set
singleton :: (Eq n, Num n) => (Int, Int) -> n -> Maybe (IntervalSet n)
singleton (start, end) n =
  if start >= end || n == 0
    then Nothing
    else Just $ IntervalSet $ IntMap.singleton start (end, n)

-- | O(n). To an IntervalTable
toIntervalTable :: Int -> IntervalSet Int -> IntervalTable
toIntervalTable domainSize (IntervalSet intervals) =
  let FoldState table occupiedSize = IntMap.foldlWithKey' step (FoldState mempty 0) intervals
   in IntervalTable domainSize occupiedSize table
  where
    step :: FoldState -> Int -> (Int, Int) -> FoldState
    step (FoldState acc occupiedSize) start (end, _) =
      FoldState
        (IntMap.insert start (end, start - occupiedSize) acc) -- insert the total size of "holes" before this interval
        (occupiedSize + end - start)

--------------------------------------------------------------------------------

-- | Whether to normalize after insertion
normalizeAfterInsert :: Bool
normalizeAfterInsert = True

-- | O(min(n, W)): Insert an interval into an interval set
insert :: (Num n, Eq n) => Interval -> n -> IntervalSet n -> IntervalSet n
insert _ 0 (IntervalSet xs) = IntervalSet xs
insert (start, end) count (IntervalSet xs) =
  if start == end
    then IntervalSet xs
    else
      let actions = calculateActionInit (start, end) count (IntervalSet xs)
       in if normalizeAfterInsert
            then normalize $ executeActions actions (IntervalSet xs)
            else executeActions actions (IntervalSet xs)

-- | O(n): Multiply the count of all intervals by a number
multiplyBy :: (Num n, Eq n) => n -> IntervalSet n -> IntervalSet n
multiplyBy 0 _ = error "[ panic ] IntervalSet: multiplyBy 0"
multiplyBy 1 (IntervalSet xs) = IntervalSet xs
multiplyBy n (IntervalSet xs) = IntervalSet (fmap (\(end, count) -> (end, count * n)) xs)

-- | O(1): Get the first offset of an interval set
getStartOffset :: IntervalSet n -> Maybe Int
getStartOffset (IntervalSet xs) = fst <$> IntMap.lookupMin xs

-- | O(n): Compute the total count of all intervals (for testing purposes)
totalCount :: (Num n) => IntervalSet n -> n
totalCount (IntervalSet xs) = IntMap.foldlWithKey' (\acc start (end, count) -> acc + count * fromIntegral (end - start)) 0 xs

-- | O(n): See if the interval set empty
null :: (Num n, Eq n) => IntervalSet n -> Bool
null (IntervalSet xs) = IntMap.null xs

-- | O(min(n, W)): Look up the count of a variable in the interval set
lookup :: IntervalSet n -> Int -> Maybe n
lookup (IntervalSet xs) x = case IntMap.lookupLE x xs of
  Nothing -> Nothing
  Just (_, (end, count)) -> if x < end then Just count else Nothing

-- | O(min(n, W)): Check if a variable occurred (i.e. count /= 0) in the interval set
member :: (Eq n, Num n) => IntervalSet n -> Int -> Bool
member (IntervalSet xs) x = case IntMap.lookupLE x xs of
  Nothing -> False
  Just (_, (end, count)) -> x < end && count /= 0

-- | Given an interval, return a list of intervals that occurred (i.e. count /= 0) in this interval
intervalsWithin :: (Eq n, Num n) => IntervalSet n -> (Int, Int) -> Seq (Int, Int)
intervalsWithin (IntervalSet xs) (start, end) =
  let (_, rest) = split (IntervalSet xs) start
      (IntervalSet middle, _) = split rest end
   in Seq.fromList $ map (\(start', (end', _)) -> (start', end')) $ IntMap.toList middle

-- | Split an IntervalSet into two at a given point
split :: (Eq n, Num n) => IntervalSet n -> Int -> (IntervalSet n, IntervalSet n)
split (IntervalSet xs) pos =
  let -- split the map into three parts: before "pos", at "pos", after "pos"
      (before, middle, after) = IntMap.splitLookup pos xs
   in case middle of
        Just (moddleEnd, middleCount) ->
          -- there happens to be an interval at "pos"
          (IntervalSet before, IntervalSet $ IntMap.insert pos (moddleEnd, middleCount) after)
        Nothing ->
          -- see if there is an interval in the "before" part that overlaps with "pos"
          case IntMap.maxViewWithKey before of
            Just ((start, (end, count)), beforeBefore) ->
              if end > pos && count /= 0
                then (IntervalSet (IntMap.insert start (pos, count) beforeBefore), IntervalSet (IntMap.insert pos (end, count) after))
                else (IntervalSet before, IntervalSet after)
            Nothing ->
              (IntervalSet mempty, IntervalSet xs) -- no interval before "pos"

-- | O(n): Merge two interval maps
merge :: (Num n, Eq n) => IntervalSet n -> IntervalSet n -> IntervalSet n
merge (IntervalSet xs) (IntervalSet ys) = normalize $ IntervalSet $ IntMap.fromDistinctAscList $ mergeIntervalList (IntMap.toAscList xs) (IntMap.toAscList ys)

-- | O(n): Merge two interval lists
mergeIntervalList :: (Num n) => [(Int, (Int, n))] -> [(Int, (Int, n))] -> [(Int, (Int, n))]
mergeIntervalList [] [] = []
mergeIntervalList [] ys = ys
mergeIntervalList xs [] = xs
mergeIntervalList ((start1, (end1, count1)) : xss) ((start2, (end2, count2)) : yss) = case start1 `compare` start2 of
  LT -> case end1 `compare` end2 of
    LT ->
      if end1 <= start2
        then --
        --  xs  ├───┤
        --  ys          ├───┤
          (start1, (end1, count1)) : mergeIntervalList xss ((start2, (end2, count2)) : yss)
        else --
        --  xs  ├───┼───┤
        --  ys      ├───┼───┤
          (start1, (start2, count1)) : (start2, (end1, count1 + count2)) : mergeIntervalList xss ((end1, (end2, count2)) : yss)
    EQ ->
      --  xs  ├───┼───┤
      --  ys      ├───┤
      (start1, (start2, count1)) : (start2, (end2, count1 + count2)) : mergeIntervalList xss yss
    GT ->
      --  xs  ├───┼───┼───┤
      --  ys      ├───┤
      (start1, (start2, count1)) : (start2, (end2, count1 + count2)) : mergeIntervalList ((end2, (end1, count1)) : xss) yss
  EQ -> case end1 `compare` end2 of
    LT ->
      --  xs  ├───┤
      --  ys  ├───┼───┤
      (start1, (end1, count1 + count2)) : mergeIntervalList xss ((end1, (end2, count2)) : yss)
    EQ ->
      --  xs  ├───────┤
      --  ys  ├───────┤
      (start1, (end1, count1 + count2)) : mergeIntervalList xss yss
    GT ->
      --  xs  ├───┼───┤
      --  ys  ├───┤
      (start2, (end2, count1 + count2)) : mergeIntervalList ((end2, (end1, count1)) : xss) yss
  GT -> case end1 `compare` end2 of
    LT ->
      --  xs      ├───┤
      --  ys  ├───┼───┼───┤
      (start2, (start1, count2)) : (start1, (end1, count1 + count2)) : mergeIntervalList xss ((end1, (end2, count2)) : yss)
    EQ ->
      --  xs      ├───┤
      --  ys  ├───┼───┤
      (start2, (start1, count2)) : (start1, (end1, count1 + count2)) : mergeIntervalList xss yss
    GT ->
      if end2 <= start1
        then --
        --  xs          ├───┤
        --  ys  ├───┤
          (start2, (end2, count2)) : mergeIntervalList ((start1, (end1, count1)) : xss) yss
        else --
        --  xs      ├───┼───┤
        --  ys  ├───┼───┤
          (start2, (start1, count2)) : (start1, (end2, count1 + count2)) : mergeIntervalList ((end2, (end1, count1)) : xss) yss

-- | O(n): Normalizes an interval set by:
--      1. concatenating adjacent intervals with the same count
--      2. removing intervals with zero count
--      3. removing intervals with zero length
normalize :: (Eq n, Num n) => IntervalSet n -> IntervalSet n
normalize = IntervalSet . IntMap.fromDistinctAscList . normalizeList . IntMap.toDescList . unIntervalSet
  where
    -- input: reversed (descending) list
    -- output: ascending list
    normalizeList :: (Eq n, Num n) => [(Int, (Int, n))] -> [(Int, (Int, n))]
    normalizeList = step []

    step :: (Eq n, Num n) => [(Int, (Int, n))] -> [(Int, (Int, n))] -> [(Int, (Int, n))]
    step acc [] = acc
    step [] ((start, (end, count)) : xs) =
      if start == end || count == 0 -- see if the coming interval is empty
        then step [] xs
        else step [(start, (end, count))] xs
    step ((start2, (end2, count2)) : acc) ((start1, (end1, count1)) : xs) =
      if start1 == end1 || count1 == 0 -- see if the coming interval is empty
        then step ((start2, (end2, count2)) : acc) xs
        else
          if end1 == start2 && count1 == count2
            then step ((start1, (end2, count1)) : acc) xs
            else step ((start1, (end1, count1)) : (start2, (end2, count2)) : acc) xs

--------------------------------------------------------------------------------

data Error n
  = OverlappingIntervals Interval Interval -- two intervals overlap
  | WidthlessInterval -- length == 0
  | ZeroedInterval -- count == 0
  | UnmergedIntervals Interval Interval n -- adjacent intervals with the same count are not merged
  deriving (Eq, Show)

-- | O(n): Check if a IntervalSet is valid
validate :: (Eq n, Num n) => IntervalSet n -> Maybe (Error n)
validate (IntervalSet xs) = case IntMap.foldlWithKey' step NotStarted xs of
  NotStarted -> Nothing -- vacously true
  Invalid err -> Just err
  Valid _ _ -> Nothing
  where
    step :: (Eq n, Num n) => Validity n -> Int -> (Int, n) -> Validity n
    step _ _ (_, 0) = Invalid ZeroedInterval -- no interval has 0 count
    step NotStarted start (end, count) =
      if start < end
        then Valid (start, end) count
        else Invalid WidthlessInterval -- no interval has 0 length
    step (Invalid err) _ _ = Invalid err
    step (Valid (prevStart, prevEnd) prevCount) start (end, count) = case prevEnd `compare` start of
      LT ->
        if start < end
          then Valid (start, end) count
          else Invalid WidthlessInterval -- no interval has 0 length
      EQ ->
        if prevCount /= count
          then Valid (start, end) count
          else Invalid (UnmergedIntervals (prevStart, prevEnd) (start, end) count) -- adjacent intervals with the same count are not merged
      GT -> Invalid (OverlappingIntervals (prevStart, prevEnd) (start, end)) -- no two intervals overlap

-- | O(n): Check if these intervals are valid (for testing purposes)
--   Invariants:
--      1. no two intervals overlap
--      2. no interval has 0 length
--      3. no interval has 0 count
--      4. adjacent intervals with the same count are be merged
isValid :: (Eq n, Num n) => IntervalSet n -> Bool
isValid = (==) Nothing . validate

data Validity n
  = NotStarted
  | Invalid (Error n)
  | Valid
      Interval -- previous interval
      n -- previous count

--------------------------------------------------------------------------------

data Case
  = -- A < X, A < Y, B < X, B < Y
    --     A   B
    --     ├───┤
    --             ├───┤
    --             X   Y
    CaseL1
  | -- A < X, A < Y, B = X, B < Y
    --   A   B
    --   ├───┤
    --       ├───┤
    --       X   Y
    CaseL2
  | -- A < X, A < Y, B > X, B < Y
    --     A       B
    --     ├───────┤
    --         ├───────┤
    --         X       Y
    CaseL3
  | -- A < X, A < Y, B > X, B = Y
    --     A       B
    --     ├───────┤
    --         ├───┤
    --         X   Y
    CaseL4
  | -- A < X, A < Y, B > X, B > Y
    --     A           B
    --     ├───────────┤
    --         ├───┤
    --         X   Y
    CaseL5
  | -- A = X, A < Y, B > X, B < Y
    --     A   B
    --     ├───┤
    --     ├───────┤
    --     X       Y
    CaseM1
  | -- A = X, A < Y, B > X, B = Y
    --     A       B
    --     ├───────┤
    --     ├───────┤
    --     X       Y
    CaseM2
  | -- A = X, A < Y, B > X, B > Y
    --     A       B
    --     ├───────┤
    --     ├───┤
    --     X   Y
    CaseM3
  | -- A > X, A < Y, B > X, B < Y
    --         A   B
    --         ├───┤
    --     ├───────────┤
    --     X           Y
    CaseR5
  | -- A > X, A < Y, B > X, B = Y
    --         A   B
    --         ├───┤
    --     ├───────┤
    --     X       Y
    CaseR4
  | -- A > X, A < Y, B > X, B > Y
    --         A       B
    --         ├───────┤
    --     ├───────┤
    --     X       Y
    CaseR3
  | -- A > X, A = Y, B > X, B > Y
    --         A   B
    --         ├───┤
    --     ├───┤
    --     X   Y
    CaseR2
  | -- A > X, A > Y, B > X, B > Y
    --             A   B
    --             ├───┤
    --     ├───┤
    --     X   Y
    CaseR1
  | --
    --             A   B
    --             ├───┤
    CaseEmpty

-- | O(min(n, W)): Analyze the case of an interval in an interval set
caseAnalysis :: Interval -> IntervalSet n -> Case
caseAnalysis (a, b) (IntervalSet xs) = case IntMap.lookupLT a xs of
  Nothing -> case IntMap.lookupGE a xs of
    Nothing -> CaseEmpty
    Just (x, (y, _)) ->
      if a == x
        then case b `compare` y of
          LT -> CaseM1
          EQ -> CaseM2
          GT -> CaseM3
        else case b `compare` x of
          LT -> CaseL1
          EQ -> CaseL2
          GT -> case b `compare` y of
            LT -> CaseL3
            EQ -> CaseL4
            GT -> CaseL5
  Just (_, (y, _)) -> case a `compare` y of
    LT -> case b `compare` y of
      LT -> CaseR5
      EQ -> CaseR4
      GT -> CaseR3
    EQ -> CaseR2
    GT -> CaseR1

--------------------------------------------------------------------------------

-- | Actions to be executed on an interval set
data Action n
  = InsertNew
      Interval -- interval to be inserted
      n -- count
  deriving (Eq, Show)

-- | Calculate the actions needed to insert an interval into an interval set
calculateActionInit :: (Num n, Eq n) => Interval -> n -> IntervalSet n -> [Action n]
calculateActionInit inserted@(start, end) count (IntervalSet xs) = case IntMap.lookupLT start xs of
  Nothing ->
    --   inserted      ├─────────────────┤
    --   existing
    calculateActionAfter
      inserted
      count
      (IntervalSet xs)
  Just (existingStart, (existingEnd, existingCount)) -> case start `compare` existingEnd of
    LT ->
      case end `compare` existingEnd of
        LT ->
          -- inserted            ╠═════╣
          -- existing      ├─────╠═════╣─────┤
          --    parts         1     2     3

          let insertPart1 = InsertNew (existingStart, start) existingCount
              insertPart2 = InsertNew (start, end) (existingCount + count)
              insertPart3 = InsertNew (end, existingEnd) existingCount
           in [insertPart1, insertPart2, insertPart3]
        EQ ->
          -- inserted            ╠═════╣
          -- existing      ├─────╠═════╣
          --    parts         1     2

          let insertPart1 = InsertNew (existingStart, start) existingCount
              insertPart2 = InsertNew (start, existingEnd) (existingCount + count)
           in case IntMap.lookup end xs of
                Nothing -> [insertPart1, insertPart2]
                Just (nextEnd, nextCount) ->
                  if existingCount + count == nextCount
                    then [insertPart1, InsertNew (start, nextEnd) (existingCount + count), InsertNew (end, nextEnd) 0]
                    else [insertPart1, insertPart2]
        GT ->
          -- inserted            ╠═════╣─────┤
          -- existing      ├─────╠═════╣
          --    parts         1     2

          let insertPart1 = InsertNew (existingStart, start) existingCount
              insertPart2 = InsertNew (start, existingEnd) (existingCount + count)
              restActions = calculateActionAfter (existingEnd, end) count (IntervalSet xs)
           in insertPart1 : insertPart2 : restActions
    EQ ->
      -- inserted                  ├─────┤
      -- existing      ├───────────┤
      if count == existingCount
        then calculateActionAfter (existingStart, end) count (IntervalSet (IntMap.delete existingStart xs))
        else calculateActionAfter inserted count (IntervalSet xs)
    GT ->
      -- inserted                  ├─────┤
      -- existing      ├─────┤
      calculateActionAfter inserted count (IntervalSet xs)

-- | Calculate the actions needed to insert an interval into an interval set with existing intervals after it
calculateActionAfter :: (Num n, Eq n) => Interval -> n -> IntervalSet n -> [Action n]
calculateActionAfter inserted@(start, end) count (IntervalSet xs) = case IntMap.lookupGE start xs of
  Nothing ->
    -- inserted          ├─────────────────┤
    -- existing
    [InsertNew inserted count]
  Just (existingStart, (existingEnd, existingCount)) -> case end `compare` existingStart of
    LT ->
      -- inserted      ├─────┤
      -- existing                  ├─────┤
      [InsertNew inserted count]
    EQ ->
      -- inserted      ├───────────┤
      -- existing                  ├─────┤
      if count == existingCount
        then [InsertNew (start, existingEnd) count, InsertNew (existingStart, existingEnd) 0]
        else [InsertNew inserted count]
    GT -> case end `compare` existingEnd of
      LT -> case start `compare` existingStart of
        LT ->
          -- inserted      ├─────╠═════╣
          -- existing            ╠═════╣─────┤
          --    parts         1     2     3
          let insertPart1 = InsertNew (start, existingStart) count
              insertPart2 = InsertNew (existingStart, end) (existingCount + count)
              insertPart3 = InsertNew (end, existingEnd) existingCount
           in [insertPart1, insertPart2, insertPart3]
        EQ ->
          -- inserted      ╠═══════════╣
          -- existing      ╠═══════════╣─────┤
          --    parts            1        2
          let insertPart1 = InsertNew (start, end) (existingCount + count)
              insertPart2 = InsertNew (end, existingEnd) existingCount
           in [insertPart1, insertPart2]
        GT ->
          -- inserted            ╠═════╣
          -- existing      ├─────╠═════╣─────┤
          --    parts         1     2     3
          let insertPart1 = InsertNew (existingStart, start) count
              insertPart2 = InsertNew (start, end) (existingCount + count)
              insertPart3 = InsertNew (end, existingEnd) existingCount
           in [insertPart1, insertPart2, insertPart3]
      EQ ->
        -- inserted      ├─────╠═════╣
        -- existing            ╠═════╣
        --    parts         1     2
        let insertPart1 = InsertNew (start, existingStart) count
            insertPart2 = InsertNew (existingStart, end) (existingCount + count)
         in -- lookahead to merge possible adjecent intervals
            case IntMap.lookup end xs of
              Nothing -> [insertPart1, insertPart2]
              Just (nextEnd, nextCount) ->
                if existingCount + count == nextCount
                  then [insertPart1, InsertNew (existingStart, nextEnd) (existingCount + count), InsertNew (end, nextEnd) 0]
                  else [insertPart1, insertPart2]
      GT ->
        --     inserted      ├─────╠═════╣─────┤
        --     existing            ╠═════╣
        --        parts         1     2     3

        let insertPart1 = InsertNew (start, existingStart) count
            insertPart2 = InsertNew (existingStart, existingEnd) (existingCount + count)
            restActions = calculateActionAfter (existingEnd, end) count (IntervalSet xs)
         in insertPart1 : insertPart2 : restActions

-- | Execute a list of actions on an interval set
executeActions :: (Eq n, Num n) => [Action n] -> IntervalSet n -> IntervalSet n
executeActions actions (IntervalSet set) = IntervalSet $ List.foldl' step set actions
  where
    step :: (Eq n, Num n) => IntMap (Int, n) -> Action n -> IntMap (Int, n)
    step xs (InsertNew (start, end) count) =
      if start == end
        then xs
        else
          if count == 0
            then IntMap.delete start xs
            else IntMap.insert start (end, count) xs

--------------------------------------------------------------------------------

-- | Temporary data structure for constructing an IntervalTable
data FoldState = FoldState
  { -- | The resulting table
    _stateTable :: IntMap (Int, Int),
    -- | The total size of intervals so far
    _stateEndOfLastInterval :: Int
  }
