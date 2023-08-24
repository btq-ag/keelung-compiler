{-# LANGUAGE DeriveGeneric #-}

-- | Module for RefB bookkeeping
module Keelung.Compiler.Optimize.OccurB (OccurB, new, null, toList, toIndexTable, increase, decrease, occuredSet) where

import Control.Arrow (Arrow (first))
import Control.DeepSeq (NFData)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.IndexTable (IndexTable)
import Keelung.Compiler.Compile.IndexTable qualified as IndexTable
import Keelung.Data.Reference
import Keelung.Syntax (Var)
import Keelung.Syntax.Counters
import Prelude hiding (null)

newtype OccurB = MapB (IntMap Int)
  deriving (Eq, Generic)

instance NFData OccurB

-- | O(1). Construct an empty OccurB
new :: Bool -> OccurB
new _useVector = MapB mempty

-- | O(1). Test whether a OccurB is empty
null :: OccurB -> Bool
null (MapB xs) = IntMap.null xs

-- | O(1).  To a list of (RefB, Int) pairs
toList :: OccurB -> [(RefB, Int)]
toList (MapB xs) = map (first RefBX) $ IntMap.toList xs

-- | O(lg n). To an IndexTable
toIndexTable :: Counters -> OccurB -> IndexTable
toIndexTable counters (MapB xs) = IndexTable.fromOccurrenceMap 1 (getCount counters (Intermediate, ReadBool), xs)

-- toIndexTable (MapB xs) = IndexTable.fromOccurrenceMap xs

-- | O(1). Bump the count of a RefB
increase :: Var -> OccurB -> OccurB
increase var (MapB xs) = MapB $ IntMap.insertWith (+) var 1 xs

-- | O(1). Decrease the count of a RefB
decrease :: Var -> OccurB -> OccurB
decrease var (MapB xs) = MapB $ IntMap.adjust (\count -> pred count `max` 0) var xs

occuredSet :: OccurB -> IntSet
occuredSet (MapB xs) = IntMap.keysSet $ IntMap.filter (> 0) xs