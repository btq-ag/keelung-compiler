{-# LANGUAGE DeriveGeneric #-}

-- | Module for RefUBits bookkeeping
module Keelung.Compiler.Optimize.OccurUB
  ( OccurUB,
    new,
    -- member,
    -- size,
    null,
    -- fromIntervalSet,
    -- toIntervalTable
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
import Keelung.Data.Reference
import Prelude hiding (null)

newtype OccurUB = OccurUB (IntMap (IntMap IntervalSet)) -- width to var to intervals of (start, length)
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
                    ( \(width, varMap) ->
                        "UInt bits "
                          <> show width
                          <> ": "
                          <> showList'
                            ( map
                                (\(var, intervals) -> show (RefUX width var) <> ": " <> show intervals)
                                (IntMap.toList varMap)
                            )
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

-- -- | O(min(n, W)): Is this Limb bit used somewhere?
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

-- -- | O(n): Get a IntMap (key: start, value: length) of all intervals. Counts are ignored. Adjacent intervals are merged.
-- fromIntervalSet :: IntervalSet -> (Int, IntMap Int)
-- fromIntervalSet intervalSet =
--   let (acc, n, previous) = IntMap.foldlWithKey' step (mempty, 0, Nothing) $ IntervalSet.expose intervalSet
--    in case previous of
--         Nothing -> (n, acc)
--         Just (start, end) -> (n + end - start, IntMap.insert start (end - start) acc)
--   where
--     step :: (IntMap Int, Int, Maybe (Int, Int)) -> Int -> (Int, Int) -> (IntMap Int, Int, Maybe (Int, Int))
--     step (acc, n, previousInterval) start (end, _) = case previousInterval of
--       Nothing -> (acc, n, Just (start, end))
--       Just (previousStart, previousEnd) ->
--         if start == previousEnd
--           then (acc, n, Just (previousStart, end)) -- merge with previous interval
--           else (IntMap.insert previousStart (previousEnd - previousStart) acc, n + previousEnd - previousStart, Just (start, end)) -- add previous interval to acc

-- -- | O(n). To an IntervalTable
-- toIntervalTable :: OccurUB -> IntervalTable
-- toIntervalTable (OccurUB xs) = mconcat $ IntMap.elems $ IntMap.mapWithKey (\width varMaps -> mconcat $ IntMap.elems $ IntMap.map (_ width) varMaps) xs
--   where
--     convert :: Width -> (Int, IntMap Int) -> IntervalTable
--     convert width (n, intervals)

-- -- toIntervalTable :: Counters -> OccurU -> IntervalTable
-- -- toIntervalTable counters (OccurU xs) =
-- --   let bitsPart = mconcat $ IntMap.elems $ IntMap.mapWithKey (\width x -> IntervalTable.fromOccurrenceMap width (getCount counters (Intermediate, ReadUInt width), x)) xs
-- --    in bitsPart

-- | O(1). Bump the count of an interval of bits in a RefU
adjust :: Int -> Width -> Var -> (Int, Int) -> OccurUB -> OccurUB
adjust amount width var interval (OccurUB xs) = OccurUB $ IntMap.alter increase' width xs
  where
    increase' :: Maybe (IntMap IntervalSet) -> Maybe (IntMap IntervalSet)
    increase' Nothing = Just $ IntMap.singleton var $ IntervalSet.adjust interval amount IntervalSet.new
    increase' (Just varMap) = Just $ IntMap.alter increase'' var varMap

    increase'' :: Maybe IntervalSet -> Maybe IntervalSet
    increase'' Nothing = Just $ IntervalSet.adjust interval amount IntervalSet.new
    increase'' (Just intervals) = Just $ IntervalSet.adjust interval amount intervals

-- | O(1). Increase the count of an interval of bits in a RefU
increase :: Width -> Var -> (Int, Int) -> OccurUB -> OccurUB
increase = adjust 1

-- | O(1). Decrease the count of an interval of bits in a RefU
decrease :: Width -> Var -> (Int, Int) -> OccurUB -> OccurUB
decrease = adjust (-1)
