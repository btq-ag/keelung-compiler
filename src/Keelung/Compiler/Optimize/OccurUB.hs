{-# LANGUAGE DeriveGeneric #-}

-- | Module for RefUBits bookkeeping
module Keelung.Compiler.Optimize.OccurUB
  ( OccurUB,
    new,
    member,
    size,
    null,
    fromIntervalSet,
    -- new,
    -- toList,
    -- toIntMap,
    -- toIndexTable,
    -- increase,
    -- decrease,
    -- occuredSet,
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

newtype OccurUB = OccurUB (IntMap (IntMap (IntMap Int))) -- width to var to intervals of (start, length)
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
                                (\(var, intervals) -> show (RefUX width var) <> ": " <> showIntervals intervals)
                                (IntMap.toList varMap)
                            )
                    )
                    (IntMap.toList xs)
                )
            )
    where
      showIntervals :: IntMap Int -> String
      showIntervals = showList' . map (\(start, len) -> show start <> " ~ " <> show (start + len)) . IntMap.toList

-- | O(1). Construct an empty OccurUB
new :: OccurUB
new = OccurUB mempty

-- | O(min(n, W)): Is this Limb bit used somewhere?
member :: OccurUB -> Width -> Var -> Int -> Bool
member (OccurUB xs) width var index = case IntMap.lookup width xs of
  Nothing -> False
  Just varMap -> case IntMap.lookup var varMap of
    Nothing -> False
    Just intervals -> case IntMap.lookupLE index intervals of
      Nothing -> False
      Just (start, len) -> start <= index && index < start + len

-- | O(min(n, W)): Get the total number of bits used in this OccurUB
size :: OccurUB -> Int
size (OccurUB xs) = IntMap.foldl' (\acc varMap -> acc + IntMap.foldl' (\acc' intervals -> acc' + sum (IntMap.elems intervals)) 0 varMap) 0 xs

-- | O(min(n, W)). Test whether a OccurUB is empty
null :: OccurUB -> Bool
null = (== 0) . size

-- | O(n): Get a IntMap (key: start, value: length) of all intervals. Counts are ignored. Adjacent intervals are merged.
fromIntervalSet :: IntervalSet -> IntMap Int
fromIntervalSet intervalSet =
  let (acc, previous) = IntMap.foldlWithKey' step (mempty, Nothing) $ IntervalSet.expose intervalSet
   in case previous of
        Nothing -> acc
        Just (start, end) -> IntMap.insert start (end - start) acc
  where
    step :: (IntMap Int, Maybe (Int, Int)) -> Int -> (Int, Int) -> (IntMap Int, Maybe (Int, Int))
    step (acc, previousInterval) start (end, _) = case previousInterval of
      Nothing -> (acc, Just (start, end))
      Just (previousStart, previousEnd) ->
        if start == previousEnd
          then (acc, Just (previousStart, end)) -- merge with previous interval
          else (IntMap.insert previousStart (previousEnd - previousStart) acc, Just (start, end)) -- add previous interval to acc

-- -- -- | O(1). Construct an empty OccurU
-- -- new :: OccurU
-- -- new = OccurU mempty

-- -- -- | O(1). Test whether a OccurU is empty
-- -- null :: OccurU -> Bool
-- -- null (OccurU xs) = IntMap.null xs

-- -- -- | O(1).  To a list of (RefF, Int) pairs
-- -- toList :: OccurU -> [(Int, IntMap Int)]
-- -- toList (OccurU xs) = IntMap.toList xs

-- -- toIntMap :: OccurU -> IntMap (IntMap Int)
-- -- toIntMap (OccurU xs) = xs

-- -- -- | O(lg n). To an IndexTable
-- -- toIndexTable :: Counters -> OccurU -> IndexTable
-- -- toIndexTable counters (OccurU xs) =
-- --   let bitsPart = mconcat $ IntMap.elems $ IntMap.mapWithKey (\width x -> IndexTable.fromOccurrenceMap width (getCount counters (Intermediate, ReadUInt width), x)) xs
-- --    in bitsPart

-- -- -- | O(1). Bump the count of a RefF
-- -- increase :: Width -> Var -> OccurU -> OccurU
-- -- increase width var (OccurU xs) = case IntMap.lookup width xs of
-- --   Nothing -> OccurU $ IntMap.insert width (IntMap.singleton var 1) xs
-- --   Just existing -> OccurU $ IntMap.insert width (IntMap.insertWith (+) var 1 existing) xs

-- -- -- | O(1). Decrease the count of a RefF
-- -- decrease :: Width -> Var -> OccurU -> OccurU
-- -- decrease width var (OccurU xs) = OccurU $ IntMap.adjust (IntMap.adjust (\count -> pred count `max` 0) var) width xs

-- -- occuredSet :: OccurU -> IntMap IntSet
-- -- occuredSet (OccurU xs) = IntMap.map (IntMap.keysSet . IntMap.filter (> 0)) xs