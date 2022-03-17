module Keelung.Constraint where

import Keelung.Constraint.CoeffMap (CoeffMap)
import Keelung.Syntax

--------------------------------------------------------------------------------

data Constraint a
  = CAdd !a !(CoeffMap a)
  | CMult !(a, Var) !(a, Var) !(a, Maybe Var)

--------------------------------------------------------------------------------
