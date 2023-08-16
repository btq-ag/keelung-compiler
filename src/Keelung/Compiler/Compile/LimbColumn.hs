module Keelung.Compiler.Compile.LimbColumn where

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

trim :: Int -> LimbColumn -> LimbColumn
trim width (LimbColumn c xs) = LimbColumn c (fmap trimLimb xs)
  where
    trimLimb :: Limb -> Limb
    trimLimb (Limb ref w offset (Left sign)) = Limb ref (w `min` width) offset (Left sign)
    trimLimb (Limb ref w offset (Right signs)) = Limb ref (w `min` width) offset (Right (take (w `min` width) signs))