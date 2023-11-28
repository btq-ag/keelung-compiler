-- For RefU Limb segement reference counting
module Keelung.Data.IntervalTree where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap

-- | Key: start of an interval
--   Value: (length of the interval, count of the interval)
--    invariant: no two intervals overlap
newtype IntervalTree = IntervalTree (IntMap (Int, Int)) deriving (Eq, Show)

type Interval = (Int, (Int, Int)) -- start, length

-- data Interval = Interval
--   { intervalStart :: Int,
--     intervalLength :: Int,
--     intervalCount :: Int
--   } deriving (Eq, Show)

new :: IntervalTree
new = IntervalTree mempty

-- lookup :: Interval -> IntervalTree -> [(Interval, Int)]
-- lookup (start, len) (IntervalTree xs) = case IntMap.lookupLE start xs of
--   Nothing ->  -- no intervals before start
--     case IntMap.lookupGT start xs of
--         Nothing -> [] -- no intervals after start
--         Just (startAfter, lenAfter) -> if startAfter < start + len -- overlap with the interval after
--             then _
--             else []
--   Just (startBefore, lenBefore) -> _

-- | Increase the count of an interval by a given amount
-- insert :: Interval -> IntervalTree -> IntervalTree
-- insert (start, (len, amount)) (IntervalTree xs) =
--   let (before, after) = IntMap.spanAntitone (>= start) xs
--    in case IntMap.lookupMax before of
--         Nothing -> case IntMap.lookupMin after of
--           Nothing -> IntervalTree $ IntMap.singleton start (len, amount)
--           Just (startAfter, (lenAfter, amountAfter)) ->
--             --      existing        ├───────────────┤
--             --      new      ├──────────────┤
--             --      paers    └───1──┴───2───┴───3───┘
--             --      existing        ├───────┤
--             --      new      ├──────────────────────┤
--             --      paers    └───1──┴───2───┴───3───┘
--             if startAfter < start + len
--               then
--               else IntervalTree $ IntMap.insert start (len, amount) xs -- no overlap
--         Just (startBefore, (lenBefore, amountBefore)) -> _

-- data Overlap
--   = NoOverlap
--       Interval -- existing               ├──────┤
--       Interval -- new      ├──────┤
--   | Overlap
--       Interval -- existing        ├─────────────┤
--       Interval -- new      ├─────────────┤
--   deriving (Eq, Show)

-- | Possible cases of overlap between the inserted interval and the existing interval before it
data OverlapBefore
  = NothingBefore
      Interval -- inserted        ├─────────────┤
  | NoOverlapBefore
      Interval -- inserted        ├─────────────┤
      Interval -- existing ├──┤
  | OverlapBefore
      Interval -- inserted        ├─────────────┤
      Interval -- existing ├─────────────┤
--   | SubsumeBefore
--       Interval -- inserted        ├─────────────┤
--       Interval -- existing        ├──────┤
  | SubsumedByBefore
      Interval -- inserted        ├─────────────┤
      Interval -- existing ├───────────────────────────┤
  deriving (Eq, Show)

lookupOverlapBefore :: Interval -> IntervalTree -> OverlapBefore
lookupOverlapBefore inserted@(start, (len, amount)) (IntervalTree xs) = case IntMap.lookupLE start xs of
  Nothing -> NothingBefore inserted
  Just before@(startBefore, (lenBefore, amountBefore)) ->
    let endBefore = startBefore + lenBefore
     in if endBefore < start
          then NoOverlapBefore inserted before
          else
            if endBefore < start + len
              then OverlapBefore inserted before
              else SubsumedByBefore inserted before

--    in case (IntMap.lookupMax before, IntMap.lookupMin after) of
--         (Nothing, Nothing) -> IntervalTree $ IntMap.singleton start (len, amount)
--         (Nothing, Just theOneAfter) -> _
--         (Just theOneBefore, Nothing) -> _
--         (Just theOneBefore, Just theOneAfter) -> _

-- | Increase the count of an interval by a given amount
-- insert :: Interval -> IntervalTree -> IntervalTree
-- insert (start, (len, amount)) xs = IntervalTree $ case lookBack start xs of
--     Nothing -> case lookAhead start xs of
--         Nothing -> IntMap.singleton start (len, amount)
--         Just _ -> _
--     Just (startBefore, lenBefore) -> _

-- -- | Lookup the interval that ends at or before the given start
-- lookBack :: Int -> IntervalTree -> Maybe Interval
-- lookBack start (IntervalTree xs) = IntMap.lookupLE start xs

-- -- | Lookup the interval that starts at or after the given start
-- lookAhead :: Int -> IntervalTree -> Maybe Interval
-- lookAhead start (IntervalTree xs) = IntMap.lookupGE start xs