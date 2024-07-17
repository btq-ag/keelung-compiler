-- | Specialized solver for polynomial equations with 2 boolean variables.
--   Intended to be qualified as `BoolBinomial`.
module Keelung.Solver.BoolBinomial (run) where

import Data.Field.Galois (GaloisField)
import Data.IntMap.Strict qualified as IntMap
import Keelung (Var)
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly

-- | Try all 4 possible assignments to the 2 boolean variables in the polynomial.
--   Return an assignment only when there's one and only one solution.
run :: (GaloisField n, Integral n) => Poly n -> Maybe ((Var, Bool), (Var, Bool))
run polynomial =
  let (constant, variables) = Poly.view polynomial
      solutions = case IntMap.toList variables of
        [(v1, c1), (v2, c2)] -> [((v1, x1), (v2, x2)) | x1 <- [False, True], x2 <- [False, True], (if x1 then c1 else 0) + (if x2 then c2 else 0) + constant == 0]
        _ -> []
   in case solutions of
        [assignment] -> Just assignment
        _ -> Nothing