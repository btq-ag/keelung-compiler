--------------------------------------------------------------------------------
--  Constraint Set Minimisation
--------------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}

module Keelung.Compiler.Optimize (run) where

import Keelung
import Keelung.Compiler.Compile.Error qualified as Compile
import Keelung.Compiler.ConstraintModule (ConstraintModule)
import Keelung.Compiler.Optimize.MinimizeConstraints qualified as MinimizeConstraints

--------------------------------------------------------------------------------

run :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Compile.Error n) (ConstraintModule n)
run = MinimizeConstraints.run

