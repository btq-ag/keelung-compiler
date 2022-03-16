module Keelung.Util where

import Data.Field.Galois (GaloisField)

-- for ease of debugging really big GF181 numbers
newtype DebugGF a = DebugGF {unDebugGF :: a}
  deriving (Eq, Ord)

instance (Show f, GaloisField f, Bounded f, Integral f) => Show (DebugGF f) where
  show (DebugGF coeff) =
    let halfway = maxBound / 2
     in if coeff >= halfway
          then show (negate (toInteger (maxBound - coeff) + 1))
          else show (toInteger coeff)
