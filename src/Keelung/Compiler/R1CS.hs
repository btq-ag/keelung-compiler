module Keelung.Compiler.R1CS where

import Data.Either (lefts, rights)
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Keelung.Compiler.Constraint hiding (numberOfConstraints)
import Keelung.Compiler.Optimise (optimiseWithWitness)
import Keelung.Compiler.Util
import Keelung.Constraint.R1C (R1C (..))
import qualified Keelung.Constraint.R1C as R1C
import Keelung.Field (N (..))
import Keelung.Types (Var)
import Keelung.Constraint.R1CS (R1CS (..))

-- | Starting from an initial partial assignment, solve the
-- constraints and return the resulting complete assignment.
-- Return `Left String` if the constraints are unsolvable.
generateWitness ::
  GaloisField n =>
  -- | Constraints to be solved
  ConstraintSystem n ->
  -- | Initial assignment
  Witness n ->
  -- | Resulting assignment
  Either (ExecError n) (Witness n)
generateWitness cs env =
  let cs' = renumberConstraints cs
      variables = [0 .. IntSet.size (csVars cs) - 1]
      (witness, _) = optimiseWithWitness env cs'
   in if all (isMapped witness) variables
        then Right witness
        else Left $ ExecVarUnassignedError [x | x <- variables, not $ isMapped witness x] witness
  where
    isMapped witness var = IntMap.member var witness

--------------------------------------------------------------------------------

-- | Returns `Nothing`    if all constraints are satisfiable,
--   returns `Just [R1C]` if at least one constraint is unsatisfiable
satisfyR1CS :: GaloisField n => Witness n -> R1CS n -> Maybe [R1C n]
satisfyR1CS witness r1cs =
  let constraints = r1csConstraints r1cs
      unsatisfiable = filter (not . flip R1C.satisfy witness) constraints
   in if null unsatisfiable
        then Nothing
        else Just unsatisfiable

-- | Converts ConstraintSystem to R1CS
toR1CS :: GaloisField n => ConstraintSystem n -> R1CS n
toR1CS cs =
  R1CS
    (rights convertedConstratins)
    (IntSet.size (csVars cs))
    (IntSet.size (csInputVars cs))
    (csBooleanInputVars cs)
    (csOutputVars cs)
    (lefts convertedConstratins)
  where
    convertedConstratins = map toR1C (Set.toList (csConstraints cs))

    toR1C :: GaloisField n => Constraint n -> Either (Var, Var) (R1C n)
    toR1C (CAdd xs) =
      Right $
        R1C
          (Left 1)
          (Right xs)
          (Left 0)
    toR1C (CMul2 aX bX cX) =
      Right $ R1C (Right aX) (Right bX) cX
    toR1C (CNQZ x m) = Left (x, m)

fromR1CS :: GaloisField n => R1CS n -> ConstraintSystem n
fromR1CS r1cs =
  ConstraintSystem
    { csConstraints =
        Set.fromList (map fromR1C (r1csConstraints r1cs))
          <> Set.fromList (map (uncurry CNQZ) (r1csCNQZPairs r1cs)),
      csBooleanInputVars = r1csBooleanInputVars r1cs,
      csVars = IntSet.fromDistinctAscList [0 .. r1csNumOfVars r1cs - 1],
      csInputVars = IntSet.fromDistinctAscList [0 .. r1csNumOfInputVars r1cs - 1],
      csOutputVars = r1csOutputVars r1cs
    }
  where
    fromR1C (R1C aX bX cX) =
      case (aX, bX, cX) of
        (Left 1, Right xs, Left 0) -> CAdd xs
        (Right xs, Left 1, Left 0) -> CAdd xs
        (Right xs, Right ys, _) -> CMul2 xs ys cX
        _ -> error "fromR1C: invalid R1C"

-- | Computes an assignment for a R1CS with given inputs
witnessOfR1CS :: GaloisField n => [n] -> R1CS n -> Either (ExecError n) (Witness n)
witnessOfR1CS inputs r1cs =
  if r1csNumOfInputVars r1cs /= length inputs
    then Left $ ExecInputUnmatchedError (r1csNumOfInputVars r1cs) (length inputs)
    else generateWitness (fromR1CS r1cs) $ IntMap.fromDistinctAscList (zip [0 ..] inputs)

--------------------------------------------------------------------------------

data ExecError n
  = ExecOutputVarsNotMappedError [Var] (IntMap n)
  | ExecOutputError [n] [n]
  | ExecR1CUnsatisfiableError [R1C n] (IntMap n)
  | ExecInputUnmatchedError Int Int
  | ExecVarUnassignedError [Var] (IntMap n)
  deriving (Eq)

instance (Show n, Bounded n, Integral n, Fractional n) => Show (ExecError n) where
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
      ++ show r1c's
      ++ "\nby the witness:\n"
      ++ show (fmap N witness)
  show (ExecInputUnmatchedError expected actual) =
    "expecting " ++ show expected ++ " input(s) but got " ++ show actual
      ++ " input(s)"
  show (ExecVarUnassignedError vars witness) =
    "these variables:\n " ++ show vars
      ++ "\n are not assigned in: \n"
      ++ show (fmap N witness)
