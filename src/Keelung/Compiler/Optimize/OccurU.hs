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
    increase,
    decrease,
  )
where

import Control.DeepSeq (NFData)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import GHC.Generics (Generic)
import Keelung (Var, Width)
import Keelung.Compiler.Util
import Keelung.Data.IntervalSet (IntervalSet)
import Keelung.Data.IntervalSet qualified as IntervalSet
import Keelung.Data.IntervalTable (IntervalTable)
import Keelung.Data.IntervalTable qualified as IntervalTable
import Prelude hiding (null)

newtype OccurU = OccurU (IntMap IntervalSet) -- IntMap of (width, IntervalSet) pairs
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
  Just intervals -> IntervalSet.member intervals (width * var + index)

-- -- | Given a Slice, return a list of Slices that are used in this OccurU
-- maskSlice :: OccurU -> Slice -> [Slice]
-- maskSlice (OccurU xs) slice = case IntMap.lookup (widthOf (Slice.sliceRefU slice)) xs of
--   Nothing -> []
--   Just intervals -> _

-- | O(min(n, W)): Get the total number of bits used in this OccurU
-- size :: OccurU -> Int
-- size (OccurU xs) = IntMap.foldl' (\acc varMap -> acc + IntMap.foldl' (\acc' (n, _) -> acc' + n) 0 varMap) 0 xs

-- | O(min(n, W)). Test whether a OccurU is empty
null :: OccurU -> Bool
null (OccurU xs) = IntMap.null xs

-- | O(n). To an IntMap of widths to IntervalTable
toIntervalTables :: OccurU -> IntMap IntervalTable
toIntervalTables (OccurU xs) = IntMap.mapWithKey IntervalSet.toIntervalTable xs

toIntervalTablesWithOffsets :: OccurU -> IntMap (Int, IntervalTable)
toIntervalTablesWithOffsets (OccurU xs) = snd $ IntMap.foldlWithKey' step (0, mempty) xs
  where
    step :: (Int, IntMap (Int, IntervalTable)) -> Width -> IntervalSet -> (Int, IntMap (Int, IntervalTable))
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

    increase' :: Maybe IntervalSet -> Maybe IntervalSet
    increase' Nothing = Just $ IntervalSet.adjust interval' amount IntervalSet.new
    increase' (Just intervalSet) = Just $ IntervalSet.adjust interval' amount intervalSet

-- | O(1). Increase the count of an interval of bits in a RefU
increase :: Width -> Var -> (Int, Int) -> OccurU -> OccurU
increase = adjust 1

-- | O(1). Decrease the count of an interval of bits in a RefU
decrease :: Width -> Var -> (Int, Int) -> OccurU -> OccurU
decrease = adjust (-1)
