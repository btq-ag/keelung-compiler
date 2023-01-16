module Keelung.Compiler.Optimize.MinimizeConstraints (run) where

import Data.Field.Galois (GaloisField)
import Keelung.Compiler.Constraint
-- import Control.Monad.State.Strict

run :: (GaloisField n, Integral n) => ConstraintSystem n -> ConstraintSystem n
run = id

------------------------------------------------------------------------------

-- type M n = State (ConstraintSystem n)