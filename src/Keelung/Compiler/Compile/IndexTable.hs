module Keelung.Compiler.Compile.IndexTable (IndexTable, empty, fromOccurrenceMap, reindex, merge) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Keelung (Width)

-------------------------------------------------------------------------------

-- | Lookup table for speeding up variable renumbering:
--   Some of the variables maybe unused, we want to remove unused variables and renumber the remaining variables so that they are contiguous.
--   To do so, we create a lookup table that keep tracks of "hole" sections in the domain.
--
--   Suppose we have 10 variables, but only some of them are used:
--
--                      0 1 2 3 4 5 6 7 8 9
--   used               x x     x x x     x
--
--                              ^         ^
--   unused so far              2         4
--
--   table: [(4, 2), (9, 4)]
--
--   we want to mark the place where the used variable segments begins, so that we can know how many unused variables are there so far.
--   So that when we want to renumber the 6th variable, we can just minus 2 from it
data IndexTable = IndexTable
  { indexTableDomainSize :: Int,
    indexTableTotalHoleSize :: Int,
    indexTableStartsWithHole :: Maybe Bool,
    indexTable :: IntMap Int
  }
  deriving (Show)

data FoldState = FoldState
  { -- | The resulting table
    _stateTable :: IntMap Int,
    -- | Are we in a hole?
    _stateInAHole :: Bool,
    -- | The number of unused variables so far
    _stateTotalHoleSize :: Int,
    -- | If the first variable is unused
    _stateStartsWithHole :: Maybe Bool
  }

instance Semigroup IndexTable where
  (<>) = merge

instance Monoid IndexTable where
  mempty = empty

-- | O(1). Construct an empty IndexTable
empty :: IndexTable
empty = IndexTable 0 0 Nothing mempty

-- | O( size of the occurence map ). Construct an IndexTable from an ocurence map
fromOccurrenceMap :: Width -> IntMap Int -> IndexTable
fromOccurrenceMap width occurrences =
  let FoldState xs _ totalHoleSize startsWithHole = IntMap.foldlWithKey' go (FoldState mempty False 0 Nothing) occurrences
      domainSize = width * IntMap.size occurrences
   in IndexTable domainSize totalHoleSize startsWithHole xs
  where
    go :: FoldState -> Int -> Int -> FoldState
    go (FoldState acc False totalHoleSize Nothing) _ count =
      if count == 0
        then FoldState acc True (totalHoleSize + width) (Just True) -- staring a new hole
        else FoldState acc False totalHoleSize (Just False) -- still not in a hole
    go (FoldState acc False totalHoleSize (Just startsWithHole)) _ count =
      if count == 0
        then FoldState acc True (totalHoleSize + width) (Just startsWithHole) -- staring a new hole
        else FoldState acc False totalHoleSize (Just startsWithHole) -- still not in a hole
    go (FoldState acc True totalHoleSize startsWithHole) var count =
      if count == 0
        then FoldState acc True (totalHoleSize + width) startsWithHole -- still in a hole
        else FoldState (IntMap.insert (var * width) totalHoleSize acc) False totalHoleSize startsWithHole -- ending the current hole

-- | O(lg n). Given an IndexTable and a variable, reindex the variable so that it become contiguous with the other variables
reindex :: IndexTable -> Int -> Int
reindex (IndexTable _ _ _ xs) var = case IntMap.lookupLE var xs of
  Nothing -> var
  Just (_, vacancyCount) -> var - vacancyCount

-- | O(lg n). Mergin two IndexTable
merge :: IndexTable -> IndexTable -> IndexTable
merge (IndexTable domainSize1 totalHoleSize1 startsWithHole1 xs1) (IndexTable domainSize2 totalHoleSize2 startsWithHole2 xs2) =
  let totalHoleSize = totalHoleSize1 + totalHoleSize2
   in IndexTable (domainSize1 + domainSize2) totalHoleSize startsWithHole1 $
        case startsWithHole2 of
          Nothing -> xs1
          Just True -> xs1 <> IntMap.mapKeys (+ domainSize1) (IntMap.map (+ totalHoleSize1) xs2)
          Just False -> xs1 <> IntMap.insert domainSize1 totalHoleSize1 (IntMap.mapKeys (+ domainSize1) (IntMap.map (+ totalHoleSize1) xs2))
