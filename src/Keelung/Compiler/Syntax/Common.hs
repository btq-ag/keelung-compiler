{-# LANGUAGE DataKinds #-}

module Keelung.Compiler.Syntax.Common where

import Data.Field.Galois (Binary, Prime)
import Data.IntMap (IntMap)

type GF64 = Binary 18446744073709551643

type GF181 = Prime 1552511030102430251236801561344621993261920897571225601

--------------------------------------------------------------------------------

type Var = Int
type Addr = Int

--------------------------------------------------------------------------------

-- A Witness is a mapping from variables to their values
type Witness n = IntMap n
