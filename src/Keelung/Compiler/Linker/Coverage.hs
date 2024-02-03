-- | Module for generating coverage information for the linker for testing purposes
module Keelung.Compiler.Linker.Coverage where

import Data.IntMap (IntMap)

type Coverage = IntMap Int

class GenerateCoverage a where
  generateCoverage :: a -> Coverage
