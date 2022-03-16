{-# LANGUAGE DataKinds #-}

module Keelung
  ( module Keelung.Monad,
    module Keelung.Syntax,
    GaloisField,
    GF64,
    GF181,
    DebugGF (..),
    Semiring (one, zero),
    module Prelude
  )
where

import Data.Field.Galois (Binary, GaloisField, Prime)
import Data.Semiring (Semiring (one, zero))
import Keelung.Monad
import Keelung.Syntax

type GF64 = Binary 18446744073709551643

type GF181 = Prime 1552511030102430251236801561344621993261920897571225601

-- for ease of debugging really big GF181 numbers
newtype DebugGF a = DebugGF {unDebugGF :: a}
  deriving (Eq, Ord)

instance (Show f, GaloisField f, Bounded f, Integral f) => Show (DebugGF f) where
  show (DebugGF coeff) =
    let halfway = maxBound / 2
     in if coeff >= halfway
          then show (negate (toInteger (maxBound - coeff) + 1))
          else show (toInteger coeff)
