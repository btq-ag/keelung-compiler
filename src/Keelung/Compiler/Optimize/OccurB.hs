{-# LANGUAGE DeriveGeneric #-}

-- | Module for RefB bookkeeping
module Keelung.Compiler.Optimize.OccurB (OccurB, new, null, toList, toIndexTable, increase, decrease, occuredSet) where

import Control.Arrow (Arrow (first))
import Control.DeepSeq (NFData)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
-- import Data.IntSet qualified as IntSet
-- import Data.Vector.Unboxed (Vector)
-- import Data.Vector.Unboxed qualified as Vec
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.IndexTable (IndexTable)
import Keelung.Compiler.Compile.IndexTable qualified as IndexTable
import Keelung.Compiler.Constraint
import Keelung.Syntax (Var)
import Keelung.Syntax.Counters
import Prelude hiding (null)

newtype OccurB
  = MapB (IntMap Int)
  deriving
    ( -- | OccurB
      --     { -- _occurBO :: !(Vector Int),
      --       -- _occurBI :: !(Vector Int),
      --       -- _occurBP :: !(Vector Int),
      --       _occurBX :: !(Vector Int)
      --     }
      Eq,
      Generic
    )

instance NFData OccurB

-- | O(1). Construct an empty OccurB
new :: Bool -> OccurB
new _useVector = MapB mempty

-- if useVector
--   then
--     OccurB
--       (Vec.replicate 100 0)
--   else MapB mempty

-- | O(1). Test whether a OccurB is empty
null :: OccurB -> Bool
null (MapB xs) = IntMap.null xs

-- null (OccurB xs) = Vec.null xs

-- null (OccurB os is ps xs) = Vec.null os && Vec.null is && Vec.null ps && Vec.null xs

-- | O(1).  To a list of (RefB, Int) pairs
toList :: OccurB -> [(RefB, Int)]
toList (MapB xs) = map (first RefBX) $ IntMap.toList xs

-- toList (OccurB xs) =
--   --   map (first RefBO) (filter notEmpty (Vec.toList (Vec.indexed os)))
--   --     ++ map (first RefBI) (filter notEmpty (Vec.toList (Vec.indexed is)))
--   --     ++ map (first RefBP) (filter notEmpty (Vec.toList (Vec.indexed ps)))
--   map (first RefBX) (filter notEmpty (Vec.toList (Vec.indexed xs)))
--   where
--     notEmpty (_, 0) = True
--     notEmpty _ = False

-- | O(lg n). To an IndexTable
toIndexTable :: Counters -> OccurB -> IndexTable
toIndexTable counters (MapB xs) = IndexTable.fromOccurrenceMap 1 (getCount counters (Intermediate, ReadBool), xs)

-- toIndexTable (MapB xs) = IndexTable.fromOccurrenceMap xs

-- | O(1). Bump the count of a RefB
increase :: Var -> OccurB -> OccurB
increase var (MapB xs) = MapB $ IntMap.insertWith (+) var 1 xs

-- increase var (OccurB xs) = OccurB (xs Vec.// [(var, succ (xs Vec.! var))])

-- increase ref (MapB xs) = MapB $ Map.insertWith (+) ref 1 xs
-- increase (RefBO i) (OccurB os is ps xs) = OccurB (os Vec.// [(i, succ (os Vec.! i))]) is ps xs
-- increase (RefBI i) (OccurB os is ps xs) = OccurB os (is Vec.// [(i, succ (is Vec.! i))]) ps xs
-- increase (RefBP i) (OccurB os is ps xs) = OccurB os is (ps Vec.// [(i, succ (ps Vec.! i))]) xs
-- increase (RefBX i) (OccurB os is ps xs) = OccurB os is ps (xs Vec.// [(i, succ (xs Vec.! i))])
-- increase (RefUBit {}) occurrences = occurrences

-- | O(1). Decrease the count of a RefB
decrease :: Var -> OccurB -> OccurB
decrease var (MapB xs) = MapB $ IntMap.adjust (\count -> pred count `max` 0) var xs

-- decrease var (OccurB xs) = OccurB (xs Vec.// [(var, 0 `max` pred (xs Vec.! var))])

-- decrease ref (MapB xs) = MapB $ Map.adjust (\count -> pred count `max` 0) ref xs
-- decrease (RefBO i) (OccurB os is ps xs) = OccurB (os Vec.// [(i, 0 `max` pred (os Vec.! i))]) is ps xs
-- decrease (RefBI i) (OccurB os is ps xs) = OccurB os (is Vec.// [(i, 0 `max` pred (is Vec.! i))]) ps xs
-- decrease (RefBP i) (OccurB os is ps xs) = OccurB os is (ps Vec.// [(i, 0 `max` pred (ps Vec.! i))]) xs
-- decrease (RefBX i) (OccurB os is ps xs) = OccurB os is ps (xs Vec.// [(i, 0 `max` pred (xs Vec.! i))])
-- decrease (RefUBit {}) occurrences = occurrences

occuredSet :: OccurB -> IntSet
occuredSet (MapB xs) = IntMap.keysSet $ IntMap.filter (> 0) xs

-- occuredSet (OccurB xs) = Vec.foldl' (\s (i, n) -> if n > 0 then IntSet.insert i s else s) IntSet.empty (Vec.indexed xs)

-- occuredSet (MapB xs) = Map.keysSet $ Map.filter (> 0) xs
-- occuredSet (OccurB os is ps xs) =
--   Vec.foldl' (\s (i, n) -> if n > 0 then Set.insert (RefBO i) s else s) Set.empty (Vec.indexed os)
--     `Set.union` Vec.foldl' (\s (i, n) -> if n > 0 then Set.insert (RefBI i) s else s) Set.empty (Vec.indexed is)
--     `Set.union` Vec.foldl' (\s (i, n) -> if n > 0 then Set.insert (RefBP i) s else s) Set.empty (Vec.indexed ps)
--     `Set.union` Vec.foldl' (\s (i, n) -> if n > 0 then Set.insert (RefBX i) s else s) Set.empty (Vec.indexed xs)