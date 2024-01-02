-- For RefU Limb segement reference counting
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Data.IntervalSet (IntervalSet, new, adjust, toIntervalTable, count, isValid) where

import Control.DeepSeq (NFData)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List qualified as List
import GHC.Generics (Generic)
import Keelung.Compiler.Util (showList')
import Keelung.Data.IntervalTable (IntervalTable (IntervalTable))

-- | Key: start of an interval
--   Value: (end of the interval, count of the interval)
--    invariant: no two intervals overlap
newtype IntervalSet = IntervalSet (IntMap (Int, Int)) deriving (Eq, Generic)

instance Show IntervalSet where
  show (IntervalSet xs) = showList' $ map (\(start, (end, _)) -> show start <> " ~ " <> show end) $ IntMap.toList xs

instance NFData IntervalSet

type Interval = (Int, Int) -- (start, end)

-- | O(1): Create an empty interval set
new :: IntervalSet
new = IntervalSet mempty

-- | O(min(n, W)): Adjust the count of an interval.
adjust :: Interval -> Int -> IntervalSet -> IntervalSet
adjust interval amount (IntervalSet xs) =
  let actions = calculateAction interval amount (IntervalSet xs)
   in executeActions actions (IntervalSet xs)

-- | O(n): Compute the total count of all intervals (for testing purposes)
count :: IntervalSet -> Int
count (IntervalSet xs) = IntMap.foldlWithKey' (\acc start (end, amount) -> acc + amount * (end - start)) 0 xs

-- | O(n). To an IntervalTable
toIntervalTable :: Int -> IntervalSet -> IntervalTable
toIntervalTable domainSize (IntervalSet intervals) =
  let FoldState table occupiedSize = IntMap.foldlWithKey' step (FoldState mempty 0) intervals
   in IntervalTable domainSize occupiedSize table
  where
    step :: FoldState -> Int -> (Int, Int) -> FoldState
    step (FoldState acc occupiedSize) start (end, _) =
      FoldState
        (IntMap.insert start (end, start - occupiedSize) acc) -- insert the total size of "holes" before this interval
        (occupiedSize + end - start)

-- | O(n): Check if these intervals are valid (for testing purposes)
--   Invariants:
--      1. no two intervals overlap
--      2. no interval has zero length
--      3. no interval has 0 count
isValid :: IntervalSet -> Bool
isValid (IntervalSet xs) = fst $ IntMap.foldlWithKey' step (True, 0) xs
  where
    step :: (Bool, Int) -> Int -> (Int, Int) -> (Bool, Int)
    step (valid, previousEnd) start (end, n) =
      ( valid && start < end && previousEnd <= start && n /= 0,
        end
      )

--------------------------------------------------------------------------------

-- | Actions to be executed on an interval set
data Action
  = InsertNew
      Interval -- interval to be inserted
      Int -- amount
  | RemoveExisting
      (Int, Int) -- interval of existing interval to be removed
  deriving (Eq, Show)

-- | Calculate the actions needed to insert an interval into an interval set
calculateAction :: Interval -> Int -> IntervalSet -> [Action]
calculateAction inserted@(start, end) amount (IntervalSet xs) = case IntMap.lookupLT start xs of
  Nothing ->
    --   inserted      ├─────────────────┤
    --   existing
    calculateActionAfter inserted amount (IntervalSet xs)
  Just (existingStart, (existingEnd, existingAmount)) ->
    if start >= existingEnd
      then --
      -- inserted                  ├─────┤
      -- existing      ├─────┤
        calculateActionAfter inserted amount (IntervalSet xs)
      else
        if end >= existingEnd
          then --
          -- inserted            ├───────────┤
          -- existing      ├───────────┤
          --            =>
          -- inserted            ╠═════╣─────┤
          -- existing      ├─────╠═════╣
          --    parts         1     2

            let removeExisting = RemoveExisting (existingStart, existingEnd)
                insertPart1 = InsertNew (existingStart, start) existingAmount
                insertPart2 = InsertNew (start, existingEnd) (existingAmount + amount)
                restActions = calculateActionAfter (existingEnd, end) amount (IntervalSet xs)
             in removeExisting : insertPart1 : insertPart2 : restActions
          else --
          -- inserted            ├─────┤
          -- existing      ├─────────────────┤
          --            =>
          -- inserted            ╠═════╣
          -- existing      ├─────╠═════╣─────┤
          --    parts         1     2     3

            let removeExisting = RemoveExisting (existingStart, existingEnd)
                insertPart1 = InsertNew (existingStart, start) existingAmount
                insertPart2 = InsertNew (start, end) (existingAmount + amount)
                insertPart3 = InsertNew (end, existingEnd) existingAmount
             in [removeExisting, insertPart1, insertPart2, insertPart3]

-- | Calculate the actions needed to insert an interval into an interval set with existing intervals after it
calculateActionAfter :: Interval -> Int -> IntervalSet -> [Action]
calculateActionAfter inserted@(start, end) amount (IntervalSet xs) = case IntMap.lookupGE start xs of
  Nothing ->
    -- inserted          ├─────────────────┤
    -- existing
    [InsertNew inserted amount]
  Just (existingStart, (existingEnd, existingAmount))
    | end <= existingStart ->
        -- inserted      ├─────┤
        -- existing                  ├─────┤
        [InsertNew inserted amount]
    | end <= existingEnd ->
        -- inserted      ├───────────┤
        -- existing            ├───────────┤
        --            =>
        -- inserted      ├─────╠═════╣
        -- existing            ╠═════╣─────┤
        --    parts         1     2     3
        let removeExisting = RemoveExisting (existingStart, existingEnd)
            insertPart1 = InsertNew (start, existingStart) amount
            insertPart2 = InsertNew (existingStart, end) (existingAmount + amount)
            insertPart3 = InsertNew (end, existingEnd) existingAmount
         in [removeExisting, insertPart1, insertPart2, insertPart3]
    | otherwise -> -- end > existingEnd
    --     inserted      ├─────────────────┤
    --     existing            ├─────┤
    --                =>
    --     inserted      ├─────╠═════╣─────┤
    --     existing            ╠═════╣
    --        parts         1     2     3
        let removeExisting = RemoveExisting (existingStart, existingEnd)
            insertPart1 = InsertNew (start, existingStart) amount
            insertPart2 = InsertNew (existingStart, existingEnd) (existingAmount + amount)
            restActions = calculateActionAfter (existingEnd, end) amount (IntervalSet xs)
         in removeExisting : insertPart1 : insertPart2 : restActions

-- | Execute a list of actions on an interval set
executeActions :: [Action] -> IntervalSet -> IntervalSet
executeActions actions (IntervalSet set) = IntervalSet $ List.foldl' step set actions
  where
    step :: IntMap Interval -> Action -> IntMap Interval
    step xs (InsertNew (start, end) amount) =
      if start == end || amount == 0
        then xs
        else IntMap.insert start (end, amount) xs
    step xs (RemoveExisting (start, end)) = case IntMap.lookup start xs of
      Nothing -> error "[ panic ] IntervalSet: trying to remove non-existing interval"
      Just (existingEnd, existingAmount) ->
        if existingEnd <= end
          then IntMap.delete start xs
          else IntMap.insert end (existingEnd, existingAmount) (IntMap.delete start xs)

--------------------------------------------------------------------------------

-- | Temporary data structure for constructing an IntervalTable
data FoldState = FoldState
  { -- | The resulting table
    _stateTable :: IntMap (Int, Int),
    -- | The total size of intervals so far
    _stateEndOfLastInterval :: Int
  }