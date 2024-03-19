{-# LANGUAGE DeriveGeneric #-}

-- | Module for RefU bookkeeping
module Keelung.Compiler.Optimize.OccurU
  ( OccurU,
    new,
    member,
    -- size,
    null,
    -- fromIntervalSet,
    toIntervalTables,
    toIntervalTablesWithOffsets,
    maskSlice,
    increase,
    decrease,
  )
where

import Control.DeepSeq (NFData)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Sequence (Seq)
import GHC.Generics (Generic)
import Keelung (Var, Width)
import Keelung.Compiler.Util
import Keelung.Data.IntervalSet (IntervalSet)
import Keelung.Data.IntervalSet qualified as IntervalSet
import Keelung.Data.IntervalTable (IntervalTable)
import Keelung.Data.IntervalTable qualified as IntervalTable
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
import Prelude hiding (null)

newtype OccurU = OccurU (IntMap (IntervalSet Int)) -- IntMap of (width, IntervalSet) pairs
  deriving (Eq, Generic)

instance NFData OccurU

instance Show OccurU where
  show (OccurU xs) =
    if null (OccurU xs)
      then ""
      else
        "  OccurrencesU:\n"
          <> indent
            ( indent
                ( unlines
                    ( map
                        ( \(width, intervalSet) ->
                            "U"
                              <> toSubscript width
                              <> ": "
                              <> show intervalSet
                        )
                        (IntMap.toList xs)
                    )
                )
            )

-- | O(1). Construct an empty OccurU
new :: OccurU
new = OccurU mempty

-- | O(min(n, W)): Is this bit used somewhere?
member :: OccurU -> Width -> Var -> Int -> Bool
member (OccurU xs) width var index = case IntMap.lookup width xs of
  Nothing -> False
  Just intervals -> case IntervalSet.lookup intervals (width * var + index) of
    Nothing -> False
    Just count -> count > 0

-- | Given a Slice, return a list of Slices that are used in this OccurU
maskSlice :: OccurU -> Width -> Var -> Slice -> Seq Slice
maskSlice (OccurU xs) width var slice =
  case IntMap.lookup width xs of
    Nothing -> mempty
    Just intervalSet ->
      let interval = ((width * var) + Slice.sliceStart slice, (width * var) + Slice.sliceEnd slice)
          intervals = IntervalSet.intervalsWithin intervalSet interval
       in fmap (\(start, end) -> slice {Slice.sliceStart = start - (width * var), Slice.sliceEnd = end - (width * var)}) intervals

-- | O(min(n, W)). Test whether a OccurU is empty
null :: OccurU -> Bool
null (OccurU xs) = IntMap.null xs

-- | O(n). To an IntMap of widths to IntervalTable
toIntervalTables :: OccurU -> IntMap IntervalTable
toIntervalTables (OccurU xs) = IntMap.mapWithKey IntervalSet.toIntervalTable xs

toIntervalTablesWithOffsets :: OccurU -> IntMap (Int, IntervalTable)
toIntervalTablesWithOffsets (OccurU xs) = snd $ IntMap.foldlWithKey' step (0, mempty) xs
  where
    step :: (Int, IntMap (Int, IntervalTable)) -> Width -> IntervalSet Int -> (Int, IntMap (Int, IntervalTable))
    step (offset, acc) width intervalSet =
      let table = IntervalSet.toIntervalTable width intervalSet
       in (offset + IntervalTable.size table, IntMap.insert width (offset, table) acc)

-- IntMap.mapWithKey IntervalSet.toIntervalTable xs

-- where
--   convert :: Width -> IntervalSet -> IntervalTable
--   convert width intervals = IntervalTable.IntervalTable width _ _

-- -- | O(n). To an IntervalTable
-- toIntervalTable :: OccurU -> IntervalTable
-- toIntervalTable (OccurU xs) = mconcat $ IntMap.elems $ IntMap.mapWithKey (\width varMaps -> mconcat $ IntMap.elems $ IntMap.map (_ width) varMaps) xs
--   where
--     convert :: Width -> (Int, IntMap Int) -> IntervalTable
--     convert width (n, intervals)

-- toIntervalTable :: Counters -> OccurU -> IntervalTable
-- toIntervalTable counters (OccurU xs) =
--   let bitsPart = mconcat $ IntMap.elems $ IntMap.mapWithKey (\width x -> IntervalTable.fromOccurrenceMap width (getCount counters (Intermediate, ReadUInt width), x)) xs
--    in bitsPart

-- | O(1). Bump the count of an interval of bits in a RefU
adjust :: Int -> Width -> Var -> (Int, Int) -> OccurU -> OccurU
adjust amount width var (start, end) (OccurU xs) = OccurU $ IntMap.alter increase' width xs
  where
    interval' :: (Int, Int)
    interval' = (width * var + start, width * var + end)

    increase' :: Maybe (IntervalSet Int) -> Maybe (IntervalSet Int)
    increase' Nothing = Just $ IntervalSet.insert interval' amount IntervalSet.new
    increase' (Just intervalSet) = Just $ IntervalSet.insert interval' amount intervalSet

-- | O(1). Increase the count of an interval of bits in a RefU
increase :: Width -> Var -> (Int, Int) -> OccurU -> OccurU
increase = adjust 1

-- | O(1). Decrease the count of an interval of bits in a RefU
decrease :: Width -> Var -> (Int, Int) -> OccurU -> OccurU
decrease = adjust (-1)
