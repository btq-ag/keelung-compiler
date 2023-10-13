module Keelung.Compiler.R1CS where

import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Keelung.Compiler.ConstraintSystem hiding (numberOfConstraints)
import Keelung.Compiler.Util
import Keelung.Constraint.R1C (R1C (..))
import Keelung.Constraint.R1C qualified as R1C
import Keelung.Constraint.R1CS (R1CS (..), toR1Cs)

--------------------------------------------------------------------------------

-- | Returns `Nothing`    if all constraints are satisfiable,
--   returns `Just [R1C]` if at least one constraint is unsatisfiable
satisfyR1CS :: (GaloisField n, Integral n) => Witness n -> R1CS n -> Maybe [R1C n]
satisfyR1CS witness r1cs =
  let constraints = toR1Cs r1cs
      unsatisfiable = filter (not . flip R1C.satisfy witness) constraints
   in if null unsatisfiable
        then Nothing
        else Just unsatisfiable

-- | Converts ConstraintSystem to R1CS
toR1CS :: GaloisField n => ConstraintSystem n -> R1CS n
toR1CS cs =
  R1CS
    { r1csField = csField cs,
      r1csConstraints = map toR1C (toList (csConstraints cs)),
      r1csCounters = csCounters cs,
      r1csEqZeros = csEqZeros cs,
      r1csDivMods = map (\(a, b, c, d) -> ([a], [b], [c], [d])) (csDivMods cs),
      r1csCLDivMods = map (\(a, b, c, d) -> ([a], [b], [c], [d])) (csCLDivMods cs),
      r1csModInvs = map (\(a, b, c, d) -> ([a], [b], [c], d)) (csModInvs cs)
    }
  where
    toR1C :: GaloisField n => Constraint n -> R1C n
    toR1C (CAdd xs) = R1C (Left 1) (Right xs) (Left 0)
    toR1C (CMul aX bX cX) = R1C (Right aX) (Right bX) cX
