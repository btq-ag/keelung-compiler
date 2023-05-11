--------------------------------------------------------------------------------
--  Constraint Set Minimisation
--------------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}

module Keelung.Compiler.Optimize (run) where

import Keelung
import Keelung.Compiler.Compile.Error qualified as Compile
import Keelung.Compiler.ConstraintSystem (ConstraintSystem)
import Keelung.Compiler.Optimize.MinimizeConstraints qualified as MinimizeConstraints

--------------------------------------------------------------------------------

run :: (GaloisField n, Integral n) => ConstraintSystem n -> Either (Compile.Error n) (ConstraintSystem n)
run = MinimizeConstraints.run

