{-# LANGUAGE DeriveGeneric #-}

-- | Module for RefF bookkeeping
module Keelung.Compiler.Optimize.OccurU
  ( OccurU,
    new,
    null,
    toList,
    toIntMap,
    toIntervalTable,
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
import Keelung.Compiler.Util
import Keelung.Data.IntervalTable (IntervalTable)
import Keelung.Data.IntervalTable qualified as IntervalTable
import Keelung.Data.Reference (RefU (RefUX))
import Keelung.Syntax (Var, Width)
import Keelung.Syntax.Counters
import Prelude hiding (null)

newtype OccurU
  = OccurU (IntMap (IntMap Int)) -- mapping of width to (mapping of var to count)
  deriving (Eq, Generic)

instance NFData OccurU

instance Show OccurU where
  show xs =
    if null xs
      then ""
      else
        "  OccurrencesU:\n  "
          <> indent
            ( showList'
                ( map
                    ( \(width, occurs) ->
                        "UInt "
                          <> show width
                          <> ": "
                          <> showList'
                            ( map
                                (\(var, n) -> show (RefUX width var) <> ": " <> show n)
                                ( filter
                                    (\(_, n) -> n > 0) -- only show variables that are used
                                    (IntMap.toList occurs)
                                )
                            )
                    )
                    (toList xs)
                )
            )

-- | O(1). Construct an empty OccurU
new :: OccurU
new = OccurU mempty

-- | O(1). Test whether a OccurU is empty
null :: OccurU -> Bool
null (OccurU xs) = IntMap.null xs

-- | O(1).  To a list of (RefF, Int) pairs
toList :: OccurU -> [(Int, IntMap Int)]
toList (OccurU xs) = IntMap.toList xs

toIntMap :: OccurU -> IntMap (IntMap Int)
toIntMap (OccurU xs) = xs

-- | O(lg n). To an IntervalTable
toIntervalTable :: Counters -> OccurU -> IntervalTable
toIntervalTable counters (OccurU xs) =
  let bitsPart = mconcat $ IntMap.elems $ IntMap.mapWithKey (\width x -> IntervalTable.fromOccurrenceMap width (getCount counters (Intermediate, ReadUInt width), x)) xs
   in bitsPart

-- | O(1). Bump the count of a RefF
increase :: Width -> Var -> OccurU -> OccurU
increase width var (OccurU xs) = case IntMap.lookup width xs of
  Nothing -> OccurU $ IntMap.insert width (IntMap.singleton var 1) xs
  Just existing -> OccurU $ IntMap.insert width (IntMap.insertWith (+) var 1 existing) xs

-- | O(1). Decrease the count of a RefF
decrease :: Width -> Var -> OccurU -> OccurU
decrease width var (OccurU xs) = OccurU $ IntMap.adjust (IntMap.adjust (\count -> pred count `max` 0) var) width xs

occuredSet :: OccurU -> IntMap IntSet
occuredSet (OccurU xs) = IntMap.map (IntMap.keysSet . IntMap.filter (> 0)) xs