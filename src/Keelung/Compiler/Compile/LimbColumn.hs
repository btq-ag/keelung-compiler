module Keelung.Compiler.Compile.LimbColumn where

import Data.Bits qualified
import Data.Sequence (Seq, (<|))
import Data.Sequence qualified as Seq
import Keelung.Data.Reference

--------------------------------------------------------------------------------

-- | A 'LimbColumn' is a sequence of 'Limb's, with a constant value.
data LimbColumn = LimbColumn
  { constant :: Integer,
    limbs :: Seq Limb
  }
  deriving (Show)

instance Semigroup LimbColumn where
  (LimbColumn const1 limbs1) <> (LimbColumn const2 limbs2) =
    LimbColumn (const1 + const2) (limbs1 <> limbs2)

instance Monoid LimbColumn where
  mempty = LimbColumn 0 mempty

--------------------------------------------------------------------------------

-- | Create a 'LimbColumn' from a constant and a list of 'Limb's.
new :: Integer -> [Limb] -> LimbColumn
new c xs = LimbColumn c (Seq.fromList xs)

isEmpty :: LimbColumn -> Bool
isEmpty (LimbColumn c xs) = c == 0 && Seq.null xs

-- | Create a 'LimbColumn' with a single 'Limb'.
singleton :: Limb -> LimbColumn
singleton x = LimbColumn 0 (pure x)

-- | Insert a 'Limb' into a 'LimbColumn'.
insert :: Limb -> LimbColumn -> LimbColumn
insert x (LimbColumn c xs) = LimbColumn c (x <| xs)

-- | Add a constant to a 'LimbColumn'.
addConstant :: Integer -> LimbColumn -> LimbColumn
addConstant c (LimbColumn c' xs) = LimbColumn (c + c') xs

-- | Trim all Limbs in a 'LimbColumn' to a given width.
trim :: Int -> LimbColumn -> LimbColumn
trim width (LimbColumn c xs) = LimbColumn c (fmap trimLimb xs)
  where
    trimLimb :: Limb -> Limb
    trimLimb (Limb ref w offset (Left sign)) = Limb ref (w `min` width) offset (Left sign)
    trimLimb (Limb ref w offset (Right signs)) = Limb ref (w `min` width) offset (Right (take (w `min` width) signs))

-- | Calculate the lower bound and upper bound
calculateBounds :: Integer -> Seq Limb -> (Integer, Integer)
calculateBounds constant = foldl step (constant, constant)
  where
    step :: (Integer, Integer) -> Limb -> (Integer, Integer)
    step (lower, upper) (Limb _ width _ (Left True)) = (lower, upper + 2 ^ width - 1)
    step (lower, upper) (Limb _ width _ (Left False)) = (lower - 2 ^ width + 1, upper)
    step (lower, upper) (Limb _ _ _ (Right xs)) = let (lower', upper') = calculateBoundsOfigns (lower, upper) xs in (lower + lower', upper + upper')

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
                  carryWidth = ceiling (logBase 2 (fromIntegral range :: Double)) :: Int
               in False : replicate (carryWidth - limbWidth - 1) True
            else
              let range = upper - lower + 2 ^ limbWidth
                  carryWidth = ceiling (logBase 2 (fromIntegral range :: Double)) :: Int
               in map (not . Data.Bits.testBit (-lower + 2 ^ limbWidth)) [limbWidth .. carryWidth - 1]
        else
          let carryWidth = ceiling (logBase 2 (fromIntegral upper :: Double)) :: Int
           in replicate (carryWidth - limbWidth) True
