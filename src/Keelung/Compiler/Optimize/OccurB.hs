{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}


-- | Module for RefB bookkeeping
module Keelung.Compiler.Optimize.OccurB (OccurB, new, null, toList, increase, decrease, occuredRefBSet) where

import Control.Arrow (Arrow (first))
import Control.DeepSeq (NFData)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Vector.Unboxed (Vector)
import Data.Vector.Unboxed qualified as Vec
import GHC.Generics (Generic)
import Keelung.Compiler.Constraint
import Keelung.Syntax.Counters
import Prelude hiding (null)

data OccurB = OccurB
  { _occurBO :: Vector Int,
    _occurBI :: Vector Int,
    _occurBP :: Vector Int,
    _occurBX :: Vector Int
  }
  deriving (Eq, Generic, NFData)

-- | O(1). Construct an empty OccurB
new :: Counters -> OccurB
new counters =
  OccurB
    (Vec.replicate (getCount counters (Output, ReadBool)) 0)
    (Vec.replicate (getCount counters (PublicInput, ReadBool)) 0)
    (Vec.replicate (getCount counters (PrivateInput, ReadBool)) 0)
    (Vec.replicate (getCount counters (Intermediate, ReadBool)) 0)

-- | O(1). Test whether a OccurB is empty
null :: OccurB -> Bool
null (OccurB os is ps xs) = Vec.null os && Vec.null is && Vec.null ps && Vec.null xs

-- | O(1).  To a list of (RefB, Int) pairs
toList :: OccurB -> [(RefB, Int)]
toList (OccurB os is ps xs) =
  map (first RefBO) (filter notEmpty (Vec.toList (Vec.indexed os)))
    ++ map (first RefBI) (filter notEmpty (Vec.toList (Vec.indexed is)))
    ++ map (first RefBP) (filter notEmpty (Vec.toList (Vec.indexed ps)))
    ++ map (first RefBX) (filter notEmpty (Vec.toList (Vec.indexed xs)))
  where
    notEmpty (_, 0) = True
    notEmpty _ = False

-- | O(1). Bump the count of a RefB
increase :: RefB -> OccurB -> OccurB
increase (RefBO i) (OccurB os is ps xs) = OccurB (os Vec.// [(i, succ (os Vec.! i))]) is ps xs
increase (RefBI i) (OccurB os is ps xs) = OccurB os (is Vec.// [(i, succ (is Vec.! i))]) ps xs
increase (RefBP i) (OccurB os is ps xs) = OccurB os is (ps Vec.// [(i, succ (ps Vec.! i))]) xs
increase (RefBX i) (OccurB os is ps xs) = OccurB os is ps (xs Vec.// [(i, succ (xs Vec.! i))])
increase (RefUBit {}) occurrences = occurrences

-- | O(1). Decrease the count of a RefB
decrease :: RefB -> OccurB -> OccurB
decrease (RefBO i) (OccurB os is ps xs) = OccurB (os Vec.// [(i, 0 `max` pred (os Vec.! i))]) is ps xs
decrease (RefBI i) (OccurB os is ps xs) = OccurB os (is Vec.// [(i, 0 `max` pred (is Vec.! i))]) ps xs
decrease (RefBP i) (OccurB os is ps xs) = OccurB os is (ps Vec.// [(i, 0 `max` pred (ps Vec.! i))]) xs
decrease (RefBX i) (OccurB os is ps xs) = OccurB os is ps (xs Vec.// [(i, 0 `max` pred (xs Vec.! i))])
decrease (RefUBit {}) occurrences = occurrences

occuredRefBSet :: OccurB -> Set RefB
occuredRefBSet (OccurB os is ps xs) =
  Vec.foldl' (\s (i, n) -> if n > 0 then Set.insert (RefBO i) s else s) Set.empty (Vec.indexed os)
    `Set.union` Vec.foldl' (\s (i, n) -> if n > 0 then Set.insert (RefBI i) s else s) Set.empty (Vec.indexed is)
    `Set.union` Vec.foldl' (\s (i, n) -> if n > 0 then Set.insert (RefBP i) s else s) Set.empty (Vec.indexed ps)
    `Set.union` Vec.foldl' (\s (i, n) -> if n > 0 then Set.insert (RefBX i) s else s) Set.empty (Vec.indexed xs)