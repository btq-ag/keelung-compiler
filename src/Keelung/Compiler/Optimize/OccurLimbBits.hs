-- | Module for RefUBits bookkeeping
module Keelung.Compiler.Optimize.OccurLimbBits () where
--   ( OccurUB,
--     new,
--     member,
--     -- new,
--     -- null,
--     -- toList,
--     -- toIntMap,
--     -- toIndexTable,
--     -- increase,
--     -- decrease,
--     -- occuredSet,
--   )
-- where

-- import Control.DeepSeq (NFData)
-- import Data.IntMap.Strict (IntMap)
-- import Data.IntMap.Strict qualified as IntMap
-- import Data.IntSet (IntSet)
-- import GHC.Generics (Generic)
-- import Keelung.Compiler.Compile.IndexTable (IndexTable)
-- import Keelung.Compiler.Compile.IndexTable qualified as IndexTable
-- import Keelung.Compiler.Util
-- import Keelung.Data.IntervalSet (IntervalSet)
-- import Keelung.Data.IntervalSet qualified as IntervalSet
-- import Keelung.Data.Reference (RefU (RefUX))
-- import Keelung.Syntax (Var, Width)
-- import Keelung.Syntax.Counters
-- import Prelude hiding (null)

-- newtype OccurUB = OccurUB (IntMap (IntMap IntervalSet)) -- width to var to intervals
--   deriving (Eq, Generic)

-- instance NFData OccurUB 

-- -- | O(1). Construct an empty OccurUB
-- new :: OccurUB
-- new = OccurUB mempty

-- -- | O(1): Is this Limb bit used somewhere?
-- member :: OccurUB -> Width -> Var -> Int -> Bool
-- member (OccurUB xs) width var index = case IntMap.lookup width xs of
--   Nothing -> False
--   Just varMap -> case IntMap.lookup var varMap of
--     Nothing -> False
--     Just intervals -> IntervalSet.member index intervals

-- -- | O(n): Get the total number of bits used in this OccurUB
-- size :: OccurUB -> Int
-- size (OccurUB xs) = IntMap.foldl' (\acc varMap -> acc + IntMap.foldl' (\acc' intervals -> acc' + IntervalSet.size intervals) 0 varMap) 0 xs

-- -- newtype OccurU
-- --   = OccurU (IntMap (IntMap Int)) -- mapping of width to (mapping of var to count)
-- --   deriving (Eq, Generic)


-- -- instance Show OccurU where
-- --   show xs =
-- --     if null xs
-- --       then ""
-- --       else
-- --         "  OccurrencesU:\n  "
-- --           <> indent
-- --             ( showList'
-- --                 ( map
-- --                     ( \(width, occurs) ->
-- --                         "UInt "
-- --                           <> show width
-- --                           <> ": "
-- --                           <> showList'
-- --                             ( map
-- --                                 (\(var, n) -> show (RefUX width var) <> ": " <> show n)
-- --                                 ( filter
-- --                                     (\(_, n) -> n > 0) -- only show variables that are used
-- --                                     (IntMap.toList occurs)
-- --                                 )
-- --                             )
-- --                     )
-- --                     (toList xs)
-- --                 )
-- --             )

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