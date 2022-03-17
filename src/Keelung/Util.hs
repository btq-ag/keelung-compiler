{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Keelung.Util where

import Data.Euclidean (Field, Euclidean, GcdDomain)
import Data.Semiring (Ring, Semiring)

-- for ease of debugging really big GF181 numbers
newtype DebugGF a = DebugGF {unDebugGF :: a}
  deriving (Eq, Ord)

-- deriving instance (Bounded n, Field n, GaloisField n) => GaloisField (DebugGF n)
deriving instance Bounded n => Bounded (DebugGF n)
deriving instance Field n => Field (DebugGF n)
deriving instance Euclidean n => Euclidean (DebugGF n)
deriving instance Ring n => Ring (DebugGF n)
deriving instance GcdDomain n => GcdDomain (DebugGF n)
deriving instance Semiring n => Semiring (DebugGF n)
deriving instance Fractional n => Fractional (DebugGF n)
deriving instance Num n => Num (DebugGF n)

-- instance (GaloisField n, Bounded n, Fractional (DebugGF n)) => GaloisField (DebugGF n) where 
--   char = char . unDebugGF
--   deg = deg . unDebugGF
--   frob = DebugGF . frob . unDebugGF

instance (Show n, Bounded n, Integral n, Fractional n) => Show (DebugGF n) where
  show (DebugGF coeff) =
    let halfway = maxBound / 2
     in if coeff >= halfway
          then show (negate (toInteger (maxBound - coeff) + 1))
          else show (toInteger coeff)