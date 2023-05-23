module Keelung.Compiler.Compile.IndexTable where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap

-------------------------------------------------------------------------------

-- | Lookup table for speeding up variable renumbering
--   Stores intervals (index, (size, vacancy count before)) of contiguous variables
--   For example, if there were 10 variables, but the 4th and 5th are unused, then the table will be
--   [(0, 0), (6, 2)]
--   So that when we want to renumber the 7th variable, we can just minus 2 from it
data IndexTable = IndexTable
  { indexTableDomainSize :: Int,
    indexTableVacancyCount :: Int,
    indexTable :: IntMap Int
  }
  deriving (Show)

-- | O(1). Construct an empty IndexTable
empty :: Int -> IndexTable
empty size = IndexTable size 0 IntMap.empty

data FoldState = FoldState
  { -- | The resulting table
    stateTable :: IntMap Int,
    -- | The latest interval (index, count) for fast lookup,
    stateHead :: Maybe (Int, Int),
    -- | The number of unused variables so far
    stateVacancyCount :: Int
  }

-- | O( size of the occurence map ). Construct an IndexTable from:
--      1. an ocurence map
--      2. the number of variables of the original domain (so that we can cap the last interval)
fromOccurrenceMap :: Int -> IntMap Int -> IndexTable
fromOccurrenceMap domainSize occurrences =
  let FoldState xs x vacancyCount = IntMap.foldlWithKey' go (FoldState mempty Nothing 0) occurrences
   in case x of
        Nothing -> IndexTable domainSize vacancyCount xs
        Just (x', c) -> IndexTable domainSize vacancyCount $ IntMap.insert x' c xs
  where
    go :: FoldState -> Int -> Int -> FoldState
    go (FoldState acc Nothing vacancyCount) var count =
      if count == 0
        then -- skip `var`, bump the vacancy count
          FoldState acc Nothing (vacancyCount + 1)
        else -- start a new interval
          FoldState acc (Just (var, 1)) vacancyCount
    go (FoldState acc (Just (previousVar, previousCount)) vacancyCount) var count =
      if count == 0
        then -- skip `var`, bump the vacancy count
          FoldState acc (Just (previousVar, previousCount)) (vacancyCount + 1)
        else -- start a new interval

          let distance = var - (previousVar + previousCount)
           in if distance == 0
                then -- continue with the privious interval
                  FoldState acc (Just (previousVar, previousCount + 1)) vacancyCount
                else -- conclude the privious interval and start a new one
                  FoldState (IntMap.insert previousVar vacancyCount acc) (Just (var, 1)) (vacancyCount + distance)

-- | O(lg n). Given an IndexTable and a variable, reindex the variable so that it become contiguous with the other variables
reindex :: IndexTable -> Int -> Int
reindex (IndexTable _ _ xs) var = case IntMap.lookupLE var xs of
  Nothing -> var
  Just (_, vacancyCount) -> var - vacancyCount