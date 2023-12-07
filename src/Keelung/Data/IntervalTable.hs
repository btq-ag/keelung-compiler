module Keelung.Data.IntervalTable (IntervalTable (IntervalTable), empty, member, size, fromOccurrenceMap, reindex, merge) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Keelung (Width)

-------------------------------------------------------------------------------

-- | This data structure serves two objectives:
--      1. Variable renumbering to make variables contiguous.
--      2. Variable membership test to check if a variable is used.
--
--   Some variables may be unused, and we want to remove those unused variables and renumber the remaining variables to ensure contiguity.
--   To achieve this, we create a lookup table that keeps track of "hole" sections in the variable space.
--
--   For example, let's consider 10 variables, but only some of them are used:
--
--                      0 1 2 3 4 5 6 7 8 9
--   Used               x x     x x x     x
--
--                      ^       ^         ^
--   Unused so far      0       2         4
--
--   We create a table with the following entries:
--      [(0, (2, 0)), (4, (6, 2)), (9, (10, 4))]
--
--   The keys represent the positions of the start of the intervals, and the values represent (end of this interval, total hole size before this interval).
--
--   We want to mark the position where the used variable segments begin, so that we can determine the number of unused variables.
--   This way, when we need to renumber the 6th variable, we can simply subtract 2 from it.
data IntervalTable = IntervalTable
  { indexTableDomainSize :: Int,
    indexTableTotalUsedVarsSize :: Int,
    indexTable :: IntMap (Int, Int)
  }
  deriving (Show, Eq)

data FoldState = FoldState
  { -- | The resulting table
    _stateTable :: IntMap (Int, Int),
    -- | The last variable that is used
    _stateLasUsedVar :: Maybe Int,
    -- | The number of used variables so far
    _stateTotalUsedVarsSize :: Int
  }

instance Semigroup IntervalTable where
  (<>) = merge

instance Monoid IntervalTable where
  mempty = empty

-- | O(1). Construct an empty IntervalTable
empty :: IntervalTable
empty = IntervalTable 0 0 mempty

-- | O(1). Is any variable within the given interval used?
--         the interval is inclusive on the left and exclusive on the right
member :: (Int, Int) -> IntervalTable -> Bool
member (start, end) (IntervalTable _ _ xs) =
  (end - start > 0)
    && case IntMap.lookupLE start xs of
      Just (_, (beforeEnd, _)) -> beforeEnd > start -- see if the end of an existing interval is within the given interval
      Nothing -> False -- no existing interval starts before the end of the given interval

-- | O(1). The number of used variables
size :: IntervalTable -> Int
size (IntervalTable _ totalUsedSize _) = totalUsedSize

-- | O(n). Construct an IntervalTable from an ocurence map
fromOccurrenceMap :: Width -> (Int, IntMap Int) -> IntervalTable
fromOccurrenceMap width (domainSize, occurrences) =
  let FoldState xs _ totalUsedSize = IntMap.foldlWithKey' go (FoldState mempty Nothing 0) occurrences
   in IntervalTable (width * domainSize) totalUsedSize xs
  where
    go :: FoldState -> Int -> Int -> FoldState
    go (FoldState acc lastUsedVar totalUsedSize) _ 0 = FoldState acc lastUsedVar totalUsedSize -- skip unused variables
    go (FoldState acc Nothing totalUsedSize) var _ = FoldState (IntMap.insert (width * var) (width * (var + 1), width * var - width * totalUsedSize) acc) (Just var) (totalUsedSize + width) -- encounted the first used variable
    go (FoldState acc (Just lastVar) totalUsedSize) var _ =
      let skippedDistance = width * (var - lastVar - 1)
       in if skippedDistance > 0
            then FoldState (IntMap.insert (width * var) (width * (var + 1), width * var - totalUsedSize) acc) (Just var) (totalUsedSize + width) -- skipped a hole
            else FoldState acc (Just var) (totalUsedSize + width) -- no hole skipped

-- | O(1). Given an IntervalTable and a variable, reindex the variable so that it become contiguous with the other variables
reindex :: IntervalTable -> Int -> Int
reindex (IntervalTable _ _ xs) var = case IntMap.lookupLE var xs of
  Nothing -> var
  Just (_, (_, vacancyCount)) -> var - vacancyCount

-- | O(n). Mergin two IntervalTable
merge :: IntervalTable -> IntervalTable -> IntervalTable
merge (IntervalTable domainSize1 totalUsedSize1 xs1) (IntervalTable domainSize2 totalUsedSize2 xs2) =
  let totalUsedSize = totalUsedSize1 + totalUsedSize2
   in IntervalTable (domainSize1 + domainSize2) totalUsedSize $ xs1 <> IntMap.mapKeys (+ domainSize1) (IntMap.map (\(end, x) -> (end + domainSize1, x + domainSize1 - totalUsedSize1)) xs2)
