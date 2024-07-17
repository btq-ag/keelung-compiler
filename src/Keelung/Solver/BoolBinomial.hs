-- | Specialized solver for polynomial equations with 2 boolean variables.
--   Intended to be qualified as `BoolBinomial`.
module Keelung.Solver.BoolBinomial (run, runWithPoly) where

import Data.Field.Galois (GaloisField)
import Data.IntMap.Strict qualified as IntMap
import Keelung (Var)
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly

-- | Try all 4 possible assignments to the 2 boolean variables in the polynomial.
--   Return an assignment only when there's one and only one solution.
run ::
  (GaloisField n, Integral n) =>
  n -> -- Coefficient `c1` of the first variable
  n -> -- Coefficient `c2` of the second variable
  n -> -- Constant term `c0`
  Maybe (Bool, Bool) -- Assignment to the 2 boolean variables `v1` and `v2`, such that `c1 * v1 + c2 * v2 + c0 = 0`
run coeff1 coeff2 constant =
  let solutions = [(x1, x2) | x1 <- [False, True], x2 <- [False, True], (if x1 then coeff1 else 0) + (if x2 then coeff2 else 0) + constant == 0]
   in case solutions of
        [assignment] -> Just assignment
        _ -> Nothing

-- | Like `run` but takes a `Poly`
runWithPoly :: (GaloisField n, Integral n) => Poly n -> Maybe ((Var, Bool), (Var, Bool))
runWithPoly polynomial =
  let (constant, variables) = Poly.view polynomial
   in case IntMap.toList variables of
        [(var1, coeff1), (var2, coeff2)] ->
          case run coeff1 coeff2 constant of
            Just (val1, val2) -> Just ((var1, val1), (var2, val2))
            Nothing -> Nothing
        _ -> Nothing