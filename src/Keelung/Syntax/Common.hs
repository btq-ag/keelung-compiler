{-# LANGUAGE DataKinds #-}

module Keelung.Syntax.Common where

import Data.Field.Galois (Binary, Prime)

type GF64 = Binary 18446744073709551643

type GF181 = Prime 1552511030102430251236801561344621993261920897571225601

--------------------------------------------------------------------------------

type Var = Int
type Addr = Int
