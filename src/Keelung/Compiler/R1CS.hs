{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.R1CS where

import Control.DeepSeq (NFData)
import Data.Either (lefts, rights)
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Serialize (Serialize)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Keelung.Compiler.Optimize (optimizeWithWitness)
import Keelung.Compiler.Relocated hiding (numberOfConstraints)
import Keelung.Compiler.Syntax.Inputs (Inputs)
import qualified Keelung.Compiler.Syntax.Inputs as Inputs
import Keelung.Compiler.Util
import Keelung.Constraint.R1C (R1C (..))
import qualified Keelung.Constraint.R1C as R1C
import Keelung.Constraint.R1CS (CNEQ (..), R1CS (..), toR1Cs)
import Keelung.Field (N (..))
import Keelung.Syntax.Counters
import Keelung.Types

-- | Starting from an initial partial assignment, solve the
-- constraints and return the resulting complete assignment.
-- Return `Left String` if the constraints are unsolvable.
generateWitness ::
  (GaloisField n, Integral n) =>
  -- | Constraints to be solved
  RelocatedConstraintSystem n ->
  -- | Initial assignment
  Witness n ->
  -- | Resulting assignment
  Either (ExecError n) (Witness n)
generateWitness cs initWit =
  let cs' = renumberConstraints cs
      variables = [0 .. getTotalCount (csCounters cs) - 1]
      (witness, _) = optimizeWithWitness initWit cs'
   in if all (isMapped witness) variables
        then Right witness
        else Left $ ExecVarUnassignedError [x | x <- variables, not $ isMapped witness x] witness
  where
    isMapped witness var = IntMap.member var witness

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
toR1CS :: GaloisField n => RelocatedConstraintSystem n -> R1CS n
toR1CS cs =
  R1CS
    { r1csConstraints = rights convertedConstratins,
      r1csCounters = csCounters cs,
      r1csCNEQs = lefts convertedConstratins
    }
  where
    convertedConstratins = map toR1C (Set.toList (csConstraints cs))

    toR1C :: GaloisField n => Constraint n -> Either (CNEQ n) (R1C n)
    toR1C (CAdd xs) =
      Right $
        R1C
          (Left 1)
          (Right xs)
          (Left 0)
    toR1C (CMul aX bX cX) =
      Right $ R1C (Right aX) (Right bX) cX
    toR1C (CNEq x) = Left x

fromR1CS :: GaloisField n => R1CS n -> RelocatedConstraintSystem n
fromR1CS r1cs =
  RelocatedConstraintSystem
    { csConstraints =
        Set.fromList (map fromR1C (r1csConstraints r1cs))
          <> Set.fromList (map CNEq (r1csCNEQs r1cs)),
      csCounters = r1csCounters r1cs
    }
  where
    fromR1C (R1C aX bX cX) =
      case (aX, bX, cX) of
        (Left 1, Right xs, Left 0) -> CAdd xs
        (Right xs, Left 1, Left 0) -> CAdd xs
        (Right xs, Right ys, _) -> CMul xs ys cX
        _ -> error "fromR1C: invalid R1C"

-- | Computes an assignment for a R1CS with given inputs
witnessOfR1CS :: (GaloisField n, Integral n) => Inputs n -> R1CS n -> Either (ExecError n) (Witness n)
witnessOfR1CS inputs r1cs =
  let inputSize = getCountBySort OfInput (r1csCounters r1cs)
   in if inputSize /= Inputs.size inputs
        then Left $ ExecInputUnmatchedError inputSize (Inputs.size inputs)
        else generateWitness (fromR1CS r1cs) (Inputs.toIntMap inputs)

--------------------------------------------------------------------------------

data ExecError n
  = ExecOutputVarsNotMappedError [Var] (IntMap n)
  | ExecOutputError [n] [n]
  | ExecR1CUnsatisfiableError [R1C n] (IntMap n)
  | ExecInputUnmatchedError Int Int
  | ExecVarUnassignedError [Var] (IntMap n)
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (ExecError n)

instance (GaloisField n, Integral n) => Show (ExecError n) where
  show (ExecOutputVarsNotMappedError vars witness) =
    "output variables "
      ++ show vars
      ++ " are not mapped in\n  "
      ++ show witness
  show (ExecOutputError expected actual) =
    "interpreted output:\n"
      ++ show (fmap N expected)
      ++ "\nactual output:\n"
      ++ show (fmap N actual)
  show (ExecR1CUnsatisfiableError r1c's witness) =
    "these R1C constraints cannot be satisfied:\n"
      ++ show (map (fmap N) r1c's)
      ++ "\nby the witness:\n"
      ++ showWitness (IntMap.restrictKeys witness (freeVarsOfR1Cs r1c's))
    where
      freeVarsOfR1Cs :: [R1C n] -> IntSet
      freeVarsOfR1Cs = IntSet.unions . map R1C.freeVars
  show (ExecInputUnmatchedError expected actual) =
    "expecting " ++ show expected ++ " input(s) but got " ++ show actual
      ++ " input(s)"
  show (ExecVarUnassignedError vars witness) =
    "these variables:\n " ++ show vars
      ++ "\n are not assigned in: \n"
      ++ showWitness (IntMap.restrictKeys witness (IntSet.fromList vars))
