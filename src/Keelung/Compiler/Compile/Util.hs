module Keelung.Compiler.Compile.Util where

import Data.Bits qualified
import Data.Sequence (Seq)
import Data.Word (Word32)
import Keelung.Data.Limb (Limb (..))
import Keelung.Data.Limb qualified as Limb

--------------------------------------------------------------------------------

-- | Calculate the number of bits required to represent an Integer.
widthOfInteger :: Integer -> Int
widthOfInteger 0 = 0
widthOfInteger x =
  let lowerBits = fromInteger x :: Word32
      higherBits = x `Data.Bits.shiftR` 32
   in if higherBits == 0
        then 32 - Data.Bits.countLeadingZeros lowerBits
        else 32 + widthOfInteger higherBits

-- | Calculate the lower bound and upper bound
calculateBounds :: Integer -> Seq Limb -> (Integer, Integer)
calculateBounds constant = foldl step (constant, constant)
  where
    step :: (Integer, Integer) -> Limb -> (Integer, Integer)
    step (lower, upper) limb = case Limb.lmbSigns limb of
      Left True -> (lower, upper + 2 ^ Limb.lmbWidth limb - 1)
      Left False -> (lower - 2 ^ Limb.lmbWidth limb + 1, upper)
      Right xs -> let (lower', upper') = calculateBoundsOfigns (lower, upper) xs in (lower + lower', upper + upper')

    calculateBoundsOfigns :: (Integer, Integer) -> [Bool] -> (Integer, Integer)
    calculateBoundsOfigns (_, _) [] = (0, 0)
    calculateBoundsOfigns (lower, upper) (True : xs) = let (lower', upper') = calculateBoundsOfigns (lower, upper) xs in (lower' * 2, upper' * 2 + 1)
    calculateBoundsOfigns (lower, upper) (False : xs) = let (lower', upper') = calculateBoundsOfigns (lower, upper) xs in (lower' * 2 - 1, upper' * 2)

-- | Calculate the carry signs of a 'LimbColumn'.
calculateCarrySigns :: Int -> Integer -> Seq Limb -> [Bool]
calculateCarrySigns limbWidth constant limbs =
  let (lower, upper) = calculateBounds constant limbs
   in if lower < 0
        then
          if (-lower) <= 2 ^ limbWidth
            then
              let range = upper + 2 ^ limbWidth
                  carryWidth = widthOfInteger range
               in False : replicate (carryWidth - limbWidth - 1) True
            else
              let range = upper - lower + 2 ^ limbWidth - 1
                  carryWidth = widthOfInteger range
               in map (not . Data.Bits.testBit (-lower + 2 ^ limbWidth)) [limbWidth .. carryWidth - 1]
        else
          let carryWidth = widthOfInteger upper
           in replicate (carryWidth - limbWidth) True
