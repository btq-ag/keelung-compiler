{-# LANGUAGE DeriveGeneric #-}

-- | Module for RefF bookkeeping
module Keelung.Compiler.Optimize.OccurF
  ( OccurF,
    new,
    null,
    toList,
    toIndexTable,
    increase,
    decrease,
    occuredSet,
  )
where

import Control.DeepSeq (NFData)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.IndexTable (IndexTable)
import Keelung.Compiler.Compile.IndexTable qualified as IndexTable
import Keelung.Syntax (Var)
import Prelude hiding (null)

newtype OccurF
  = OccurF (IntMap Int)
  deriving (Eq, Generic)

instance NFData OccurF

-- | O(1). Construct an empty OccurF
new :: OccurF
new = OccurF mempty

-- | O(1). Test whether a OccurF is empty
null :: OccurF -> Bool
null (OccurF xs) = IntMap.null xs

-- | O(1). To a list of (RefF, Int) pairs
toList :: OccurF -> [(Int, Int)]
toList (OccurF xs) = IntMap.toList xs

-- | O(lg n). To an IndexTable
toIndexTable :: OccurF -> IndexTable
toIndexTable (OccurF xs) = IndexTable.fromOccurrenceMap 1 xs

-- | O(1). Bump the count of a RefF
increase :: Var -> OccurF -> OccurF
increase var (OccurF xs) = OccurF $ IntMap.insertWith (+) var 1 xs

-- | O(1). Decrease the count of a RefF
decrease :: Var -> OccurF -> OccurF
decrease var (OccurF xs) = OccurF $ IntMap.adjust (\count -> pred count `max` 0) var xs

occuredSet :: OccurF -> IntSet
occuredSet (OccurF xs) = IntMap.keysSet $ IntMap.filter (> 0) xs