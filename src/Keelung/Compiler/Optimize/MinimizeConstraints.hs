module Keelung.Compiler.Optimize.MinimizeConstraints (run) where

import Data.Field.Galois (GaloisField)
import Keelung.Compiler.Constraint

run :: (GaloisField n, Integral n) => ConstraintSystem n -> ConstraintSystem n
run = id