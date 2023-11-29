-- For RefU Limb segement reference counting
module Keelung.Data.IntervalTree where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap

-- | Key: start of an interval
--   Value: (end of the interval, count of the interval)
--    invariant: no two intervals overlap
newtype IntervalTree = IntervalTree (IntMap (Int, Int)) deriving (Eq, Show)

type Interval = (Int, (Int, Int)) -- start, (end, amount)

new :: IntervalTree
new = IntervalTree mempty

insert :: Interval -> IntervalTree -> IntervalTree
insert interval (IntervalTree xs) =
  let actions = calculateAction interval (IntervalTree xs)
   in executeActions actions (IntervalTree xs)

data Action
  = InsertNew
      Interval -- inserted
  | RemoveExisting
      Int -- start of the existing interval

-- | Calculate the actions needed to insert an interval into an interval tree
calculateAction :: Interval -> IntervalTree -> [Action]
calculateAction inserted@(start, (end, amount)) (IntervalTree xs) = case IntMap.lookupLE start xs of
  Nothing ->
    --   inserted      ├─────────────────┤
    --   existing
    calculateActionAfter inserted (IntervalTree xs)
  Just (existingStart, (existingEnd, existingAmount)) ->
    if start >= existingEnd
      then --
      -- inserted                  ├─────┤
      -- existing      ├─────┤
        calculateActionAfter inserted (IntervalTree xs)
      else --
      -- inserted            ├───────────┤
      -- existing      ├───────────┤
      --            =>
      -- inserted            ╠═════╣─────┤
      -- existing      ├─────╠═════╣
      --    parts         1     2

        let removeExisting = RemoveExisting existingStart
            insertPart1 = InsertNew (start, (existingStart, amount))
            insertPart2 = InsertNew (existingStart, (end, existingAmount + amount))
            restActions = calculateActionAfter (existingEnd, (end, amount)) (IntervalTree xs)
         in removeExisting : insertPart1 : insertPart2 : restActions

-- | Calculate the actions needed to insert an interval into an interval tree with existing intervals after it
calculateActionAfter :: Interval -> IntervalTree -> [Action]
calculateActionAfter inserted@(start, (end, amount)) (IntervalTree xs) = case IntMap.lookupGT start xs of
  Nothing ->
    -- inserted          ├─────────────────┤
    -- existing
    [InsertNew inserted]
  Just (existingStart, (existingEnd, existingAmount))
    | end <= existingStart ->
        -- inserted      ├─────┤
        -- existing                  ├─────┤
        [InsertNew inserted]
    | end <= existingEnd ->
        -- inserted      ├───────────┤
        -- existing            ├───────────┤
        --            =>
        -- inserted      ├─────╠═════╣
        -- existing            ╠═════╣─────┤
        --    parts         1     2     3
        let removeExisting = RemoveExisting existingStart
            insertPart1 = InsertNew (start, (existingStart, amount))
            insertPart2 = InsertNew (existingStart, (end, existingAmount + amount))
            insertPart3 = InsertNew (end, (existingEnd, existingAmount))
         in [removeExisting, insertPart1, insertPart2, insertPart3]
    | otherwise -> -- end > existingEnd
    --     inserted      ├─────────────────┤
    --     existing            ├─────┤
    --                =>
    --     inserted      ├─────╠═════╣─────┤
    --     existing            ╠═════╣
    --        parts         1     2     3
        let removeExisting = RemoveExisting existingStart
            insertPart1 = InsertNew (start, (existingStart, amount))
            insertPart2 = InsertNew (existingStart, (existingEnd, existingAmount + amount))
            restParts = calculateActionAfter (existingEnd, (end, amount)) (IntervalTree xs)
         in removeExisting : insertPart1 : insertPart2 : restParts

-- | Execute a list of actions on an interval tree
executeActions :: [Action] -> IntervalTree -> IntervalTree
executeActions actions (IntervalTree tree) = IntervalTree $ foldl step tree actions
  where
    step :: IntMap (Int, Int) -> Action -> IntMap (Int, Int)
    step xs (InsertNew (index, inserted)) = IntMap.insert index inserted xs
    step xs (RemoveExisting index) = IntMap.delete index xs