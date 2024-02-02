{-# LANGUAGE DeriveGeneric #-}

-- | Module for RefUBits bookkeeping
module Keelung.Compiler.Optimize.OccurUB
  ( OccurUB,
    new,
    -- member,
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

newtype OccurUB = OccurUB (IntMap IntervalSet) -- IntMap of (width, IntervalSet) pairs
  deriving (Eq, Generic)

instance NFData OccurUB

instance Show OccurUB where
  show (OccurUB xs) =
    if null (OccurUB xs)
      then ""
      else
        "  OccurrencesUB:\n  "
          <> indent
            ( showList'
                ( map
                    ( \(width, intervalSet) ->
                        show width
                          <> ": "
                          <> show intervalSet
                          -- showList'
                          --   ( map
                          --       (\(var, intervals) -> show (RefUX width var) <> ": " <> show intervals)
                          --       (IntMap.toList varMap)
                          --   )
                    )
                    (IntMap.toList xs)
                )
            )

-- where
--   showIntervals :: IntMap Int -> String
--   showIntervals = showList' . map (\(start, len) -> show start <> " ~ " <> show (start + len)) . IntMap.toList

-- | O(1). Construct an empty OccurUB
new :: OccurUB
new = OccurUB mempty

-- | O(min(n, W)): Is this Limb bit used somewhere?
-- member :: OccurUB -> Width -> Var -> Int -> Bool
-- member (OccurUB xs) width var index = case IntMap.lookup width xs of
--   Nothing -> False
--   Just varMap -> case IntMap.lookup var varMap of
--     Nothing -> False
--     Just (_, intervals) -> case IntMap.lookupLE index intervals of
--       Nothing -> False
--       Just (start, len) -> start <= index && index < start + len

-- | O(min(n, W)): Get the total number of bits used in this OccurUB
-- size :: OccurUB -> Int
-- size (OccurUB xs) = IntMap.foldl' (\acc varMap -> acc + IntMap.foldl' (\acc' (n, _) -> acc' + n) 0 varMap) 0 xs

-- | O(min(n, W)). Test whether a OccurUB is empty
null :: OccurUB -> Bool
null (OccurUB xs) = IntMap.null xs

-- | O(n). To an IntMap of widths to IntervalTable
toIntervalTables :: OccurUB -> IntMap IntervalTable
toIntervalTables (OccurUB xs) = IntMap.mapWithKey IntervalSet.toIntervalTable xs

toIntervalTablesWithOffsets :: OccurUB -> IntMap (Int, IntervalTable)
toIntervalTablesWithOffsets (OccurUB xs) = snd $ IntMap.foldlWithKey' step (0, mempty) xs
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
-- toIntervalTable :: OccurUB -> IntervalTable
-- toIntervalTable (OccurUB xs) = mconcat $ IntMap.elems $ IntMap.mapWithKey (\width varMaps -> mconcat $ IntMap.elems $ IntMap.map (_ width) varMaps) xs
--   where
--     convert :: Width -> (Int, IntMap Int) -> IntervalTable
--     convert width (n, intervals)

-- toIntervalTable :: Counters -> OccurU -> IntervalTable
-- toIntervalTable counters (OccurU xs) =
--   let bitsPart = mconcat $ IntMap.elems $ IntMap.mapWithKey (\width x -> IntervalTable.fromOccurrenceMap width (getCount counters (Intermediate, ReadUInt width), x)) xs
--    in bitsPart

-- | O(1). Bump the count of an interval of bits in a RefU
adjust :: Int -> Width -> Var -> (Int, Int) -> OccurUB -> OccurUB
adjust amount width var (start, end) (OccurUB xs) = OccurUB $ IntMap.alter increase' width xs
  where
    interval' :: (Int, Int)
    interval' = (width * var + start, width * var + end)

    increase' :: Maybe IntervalSet -> Maybe IntervalSet
    increase' Nothing = Just $ IntervalSet.adjust interval' amount IntervalSet.new
    increase' (Just intervalSet) = Just $ IntervalSet.adjust interval' amount intervalSet

-- increase' :: Maybe (IntMap IntervalSet) -> Maybe (IntMap IntervalSet)
-- increase' Nothing = Just $ IntMap.singleton var $ IntervalSet.adjust interval amount IntervalSet.new
-- increase' (Just varMap) = Just $ IntMap.alter increase'' var varMap

-- increase'' :: Maybe IntervalSet -> Maybe IntervalSet
-- increase'' Nothing = Just $ IntervalSet.adjust interval amount IntervalSet.new
-- increase'' (Just intervals) = Just $ IntervalSet.adjust interval amount intervals

-- | O(1). Increase the count of an interval of bits in a RefU
increase :: Width -> Var -> (Int, Int) -> OccurUB -> OccurUB
increase = adjust 1

-- | O(1). Decrease the count of an interval of bits in a RefU
decrease :: Width -> Var -> (Int, Int) -> OccurUB -> OccurUB
decrease = adjust (-1)
