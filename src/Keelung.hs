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
import Keelung.Util (DebugGF(..))

type GF64 = Binary 18446744073709551643

type GF181 = Prime 1552511030102430251236801561344621993261920897571225601
