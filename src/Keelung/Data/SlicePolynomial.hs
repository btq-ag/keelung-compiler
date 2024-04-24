{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

-- | For storing Slices in a polynomial
module Keelung.Data.SlicePolynomial
  ( -- * Construction
    SlicePoly,
    new,

    -- * Conversion
    fromSlices,
    toSlices,

    -- * Update
    insert,
    insertMany,
    multiplyBy,

    -- * Query
    null,
    size,
    IntervalSet.Error (..),
    validate,
    isValid,
  )
where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.IntMap qualified as IntMap
import Data.Map (Map)
import Data.Map qualified as Map
import GHC.Generics (Generic)
import Keelung.Data.IntervalSet (IntervalSet)
import Keelung.Data.IntervalSet qualified as IntervalSet
import Keelung.Data.Reference (RefU)
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
import Prelude hiding (lookup, null)
import Prelude qualified

-- |  Representing polynomials with variables like `U₈0[0] + 2U₈0[1] + 4U₈0[2] + 8U₈0[3] + ...`.
--    Using `Slice` as the interface, and `IntervalSet n` as the underlying representation.
--
--    Note that, when merging two Slices, the multiplier of the second Slice will have to be shifted by the length of the first Slice.
--    For example, consider the following example:
--      Suppose that we now already have `U₈0[0 .. 4)` stored in the polynomial, and we want to add `U₈0[4 .. 8)` to it, we'd expect the result to be:
--        `U₈0[0] + 2U₈0[1] + 4U₈0[2] + 8U₈0[3] +   U₈0[4] +  2U₈0[5] +  4U₈0[6] +   8U₈0[7]`
--      However, if we just merge the two intervals together, we'd get:
--        `U₈0[0] + 2U₈0[1] + 4U₈0[2] + 8U₈0[3] + 16U₈0[4] + 32U₈0[5] + 64U₈0[6] + 128U₈0[7]`
--      It's because that we didn't shift the multiplier of the second interval by the length of the first interval.
newtype SlicePoly n = SlicePoly {unSlicePoly :: Map RefU (IntervalSet n)} deriving (Show, Eq, Functor, Ord, Generic)

instance (NFData n) => NFData (SlicePoly n)

instance (Integral n, GaloisField n) => Semigroup (SlicePoly n) where
  (<>) = add

instance (Integral n, GaloisField n) => Monoid (SlicePoly n) where
  mempty = new

-- | Create a new `SlicePoly` with no Slices
new :: SlicePoly n
new = SlicePoly mempty

--------------------------------------------------------------------------------

-- | Convert a list of Slices to a polynomial
fromSlices :: (Integral n, GaloisField n) => [(Slice, n)] -> SlicePoly n
fromSlices = foldr insert new

-- | Convert the polynomial to a list of Slices
toSlices :: (Integral n, GaloisField n) => SlicePoly n -> [(Slice, n)]
toSlices = concatMap (uncurry convert) . Map.toList . unSlicePoly
  where
    convert :: (Integral n, GaloisField n) => RefU -> IntervalSet n -> [(Slice, n)]
    convert ref xss = case IntMap.toList (IntervalSet.unIntervalSet xss) of
      [] -> []
      ((firstStart, (firstEnd, firstCount)) : xs) ->
        -- we need to know what's the first interval, so that we can adjust the multiplier of the rest
        (Slice.Slice ref firstStart firstEnd, firstCount)
          : map (\(start, (end, count)) -> (Slice.Slice ref start end, count * calculateMultiplier firstStart start)) xs

    -- To merge 2 Slices, we need to know the multiplier of the second Slice
    -- However, because the underlying field may be a binary field, we need to check if `2 == 0` first
    calculateMultiplier :: (Integral n, GaloisField n) => Int -> Int -> n
    calculateMultiplier prev next =
      let two = 2
       in if two == 0
            then 1
            else two ^ (next - prev)

--------------------------------------------------------------------------------

-- | Insert a Slice with a multiplier into the polynomial
insert :: (Integral n, GaloisField n) => (Slice, n) -> SlicePoly n -> SlicePoly n
insert (Slice.Slice ref start end, n) (SlicePoly xs) = case IntervalSet.singleton (start, end) n of
  Nothing -> SlicePoly xs -- no-op
  Just x -> SlicePoly (Map.insertWith mergeEntry ref x xs)

-- | Insert many Slices with multipliers into the polynomial
insertMany :: (Integral n, GaloisField n) => [(Slice, n)] -> SlicePoly n -> SlicePoly n
insertMany slices xs = foldr insert xs slices

-- | Merge two IntervalSets while maintaining the correct multiplier
mergeEntry :: (Integral n, GaloisField n) => IntervalSet n -> IntervalSet n -> IntervalSet n
mergeEntry a b = case (IntervalSet.getStartOffset a, IntervalSet.getStartOffset b) of
  (Nothing, Nothing) -> mempty
  (Just _, Nothing) -> a
  (Nothing, Just _) -> b
  (Just x, Just y) -> case notOnBinaryExtentionFields 2 of
    Nothing -> a <> b
    Just two -> case x `compare` y of
      LT -> a <> IntervalSet.multiplyBy (recip (two ^ (y - x))) b
      EQ -> a <> b
      GT -> b <> IntervalSet.multiplyBy (recip (two ^ (x - y))) a
  where
    -- on `Prime 2` and binary fields, `2 == 0` and `recip (2 ^ n)` would lead to `ArithException: divide by zero`
    -- to prevent this from happening, we first check if `2 == 0` is true
    -- the following function is for enforcing the type of `2` to be the same as the underlying field
    notOnBinaryExtentionFields x = if x == 0 then Nothing else Just x

-- | Multiply all Slices in the polynomial by a number
multiplyBy :: (Integral n, GaloisField n) => n -> SlicePoly n -> SlicePoly n
multiplyBy n = SlicePoly . fmap (IntervalSet.multiplyBy n) . unSlicePoly

-- | Add two polynomials together
add :: (Integral n, GaloisField n) => SlicePoly n -> SlicePoly n -> SlicePoly n
add (SlicePoly xs) (SlicePoly ys) = SlicePoly (Map.unionWith mergeEntry xs ys)

--------------------------------------------------------------------------------

-- | See if all Slices in the polynomial are zero
null :: (Integral n) => SlicePoly n -> Bool
null = all IntervalSet.null . unSlicePoly

-- | Get the number of Slices in the polynomial
size :: (Integral n, GaloisField n) => SlicePoly n -> Int
size = length . toSlices

-- | Check if a PolySlice is valid
validate :: (Eq n, Num n) => SlicePoly n -> [(RefU, IntervalSet.Error n)]
validate (SlicePoly xs) = Map.toList $ Map.mapMaybe IntervalSet.validate xs

-- | Check if a PolySlice is valid
isValid :: (Eq n, Num n) => SlicePoly n -> Bool
isValid = Prelude.null . validate