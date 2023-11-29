-- For RefU Limb segement reference counting
module Keelung.Data.IntervalTree (IntervalTree, new, increase, totalCount) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List qualified as List
import Debug.Trace

-- | Key: start of an interval
--   Value: (end of the interval, count of the interval)
--    invariant: no two intervals overlap
newtype IntervalTree = IntervalTree (IntMap Interval) deriving (Eq, Show)

type Interval = (Int, Int) -- start, (end, amount)

-- | O(1): Create an empty interval tree
new :: IntervalTree
new = IntervalTree mempty

-- | O(min(n, W)): Increase the count of an interval
increase :: Interval -> Int -> IntervalTree -> IntervalTree
increase interval amount (IntervalTree xs) =
  let actions = calculateAction interval amount (IntervalTree xs)
   in executeActions actions (IntervalTree xs)

-- | O(n): Compute the total count of all intervals in the tree (for testing purposes)
totalCount :: IntervalTree -> Int
totalCount (IntervalTree xs) = IntMap.foldlWithKey' (\acc start (end, amount) -> acc + amount * (end - start)) 0 xs

--------------------------------------------------------------------------------

-- | Actions to be executed on an interval tree
data Action
  = InsertNew
      Interval -- interval to be inserted
      Int -- amount
  | RemoveExisting
      (Int, Int) -- interval of existing interval to be removed
  deriving (Eq, Show)

-- | Calculate the actions needed to insert an interval into an interval tree
calculateAction :: Interval -> Int -> IntervalTree -> [Action]
calculateAction inserted@(start, end) amount (IntervalTree xs) = case IntMap.lookupLT start xs of
  Nothing ->
    --   inserted      ├─────────────────┤
    --   existing
    calculateActionAfter inserted amount (IntervalTree xs)
  Just (existingStart, (existingEnd, existingAmount)) ->
    if start >= existingEnd
      then --
      -- inserted                  ├─────┤
      -- existing      ├─────┤
        calculateActionAfter inserted amount (IntervalTree xs)
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
                restActions = calculateActionAfter (existingEnd, end) amount (IntervalTree xs)
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

-- | Calculate the actions needed to insert an interval into an interval tree with existing intervals after it
calculateActionAfter :: Interval -> Int -> IntervalTree -> [Action]
calculateActionAfter inserted@(start, end) amount (IntervalTree xs) = case IntMap.lookupGE start xs of
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
            restActions = calculateActionAfter (existingEnd, end) amount (IntervalTree xs)
         in removeExisting : insertPart1 : insertPart2 : restActions

-- | Execute a list of actions on an interval tree
executeActions :: [Action] -> IntervalTree -> IntervalTree
executeActions actions (IntervalTree tree) = IntervalTree $ List.foldl' step tree actions
  where
    step :: IntMap Interval -> Action -> IntMap Interval
    step xs (InsertNew (start, end) amount) =
      if start == end
        then xs
        else IntMap.insert start (end, amount) xs
    step xs (RemoveExisting (start, end)) = case IntMap.lookup start xs of
      Nothing -> error "[ panic ] IntervalTree: trying to remove non-existing interval"
      Just (existingEnd, existingAmount) ->
        if existingEnd <= end
          then IntMap.delete start xs
          else IntMap.insert end (existingEnd, existingAmount) $ traceShow ("delete", (start, end), xs, IntMap.delete start xs) $ IntMap.delete start xs