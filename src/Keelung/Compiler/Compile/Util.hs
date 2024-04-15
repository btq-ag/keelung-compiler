module Keelung.Compiler.Compile.Util
  ( widthOfInteger,
    calculateBounds,
    calculateCarrySigns,
    calculateSignsOfLimbs,
    rangeToBitSigns,
    bitSignsToRange,
  )
where

import Data.Bits qualified
import Data.Foldable (toList)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Keelung (Width)
import Keelung.Data.Limb (Limb (..))
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.U (widthOfInteger)
import Keelung.Syntax (widthOf)

--------------------------------------------------------------------------------

-- | Calculate the lower bound and upper bound
calculateBounds :: Integer -> Seq Limb -> (Integer, Integer)
calculateBounds constant = foldl step (constant, constant)
  where
    step :: (Integer, Integer) -> Limb -> (Integer, Integer)
    step (lower, upper) limb = case limb of
      Limb.OperandLimb _ _ _ True -> (lower, upper + 2 ^ widthOf limb - 1)
      Limb.OperandLimb _ _ _ False -> (lower - 2 ^ widthOf limb + 1, upper)
      Limb.CarryLimb _ xs -> let (lower', upper') = calculateBoundsOfSigns (lower, upper) (toList xs) in (lower + lower', upper + upper')

    calculateBoundsOfSigns :: (Integer, Integer) -> [(Bool, Int)] -> (Integer, Integer)
    calculateBoundsOfSigns (_, _) [] = (0, 0)
    calculateBoundsOfSigns (lower, upper) ((True, width) : xs) = let (lower', upper') = calculateBoundsOfSigns (lower, upper) xs in (lower' * 2 ^ width, (upper' + 1) * 2 ^ width - 1)
    calculateBoundsOfSigns (lower, upper) ((False, width) : xs) = let (lower', upper') = calculateBoundsOfSigns (lower, upper) xs in ((lower' - 1) * 2 ^ width + 1, upper' * 2 ^ width)

-- | Like `calculateBounds`, but only retain the carry bits
calculateCarrySigns :: Int -> Integer -> Seq Limb -> Limb.Signs
calculateCarrySigns limbWidth constant limbs = snd $ Limb.splitAtSigns limbWidth $ calculateSignsOfLimbs limbWidth constant limbs

-- | TODO: optimize this function (along with `calculateBounds` and `widthOfInteger` ...)
-- | Calculate the signs of bits of the summation of some Limbs and a constant
calculateSignsOfLimbs :: Int -> Integer -> Seq Limb -> Limb.Signs
calculateSignsOfLimbs limbWidth constant limbs =
  let (lower_, upper) = calculateBounds constant limbs
   in if lower_ >= 0
        then
          let width = widthOfInteger upper
           in Seq.singleton (True, width `max` limbWidth)
        else -- if the lower bound is negative, round it to the nearest multiple of `2 ^ limbWidth` smaller than it!

          let lower = (lower_ `div` (2 ^ limbWidth)) * 2 ^ limbWidth
              width = widthOfInteger (upper - lower)
              firstPart = Seq.fromList $ aggregateSigns $ map (not . Data.Bits.testBit (-lower)) [0 .. width - 1]
              secondPart = Seq.singleton (True, limbWidth - width)
           in -- pad the signs to the width of limbs if necessary
              if limbWidth - width > 0
                then firstPart Seq.>< secondPart
                else firstPart
  where
    aggregateSigns :: [Bool] -> [(Bool, Width)]
    aggregateSigns = step Nothing
      where
        step :: Maybe (Bool, Width) -> [Bool] -> [(Bool, Width)]
        step Nothing [] = []
        step Nothing (x : xs) = step (Just (x, 1)) xs
        step (Just (sign, width)) [] = [(sign, width)]
        step (Just (sign, width)) (x : xs) =
          if sign == x
            then step (Just (sign, width + 1)) xs
            else (sign, width) : step (Just (x, 1)) xs

-- | Given a range, calculate the signs of bits such that the range can be represented by the bits
rangeToBitSigns :: (Integer, Integer) -> [Bool]
rangeToBitSigns (lower, upper) =
  let range = upper - lower
      width = widthOfInteger ((-lower) `max` upper `max` range)
   in if lower >= 0
        then replicate width True
        else map (not . Data.Bits.testBit (-lower)) [0 .. width - 1]

-- | Given a list of signs of bits, calculate the range represented by the bits
bitSignsToRange :: [Bool] -> (Integer, Integer)
bitSignsToRange =
  snd
    . foldl
      ( \(index, (lower, higher)) sign ->
          if sign then (index + 1, (lower, higher + 2 ^ index)) else (index + 1, (lower - 2 ^ index, higher))
      )
      (0 :: Int, (0, 0))