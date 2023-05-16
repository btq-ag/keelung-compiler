{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.R1CS where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung.Compiler.Relocated hiding (numberOfConstraints)
import Keelung.Compiler.Util
import Keelung.Constraint.R1C (R1C (..))
import Keelung.Constraint.R1C qualified as R1C
import Keelung.Constraint.R1CS (R1CS (..), toR1Cs)
import Keelung.Field (N (..))
import Keelung.Syntax

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
    { r1csField = csField cs,
      r1csConstraints = map toR1C (toList (csConstraints cs)),
      r1csBinReps = (csBinReps cs, csBinReps' cs),
      r1csCounters = csCounters cs,
      r1csEqZeros = csEqZeros cs,
      r1csDivMods = csDivMods cs,
      r1csModInvs = csModInvs cs
    }
  where
    toR1C :: GaloisField n => Constraint n -> R1C n
    toR1C (CAdd xs) = R1C (Left 1) (Right xs) (Left 0)
    toR1C (CMul aX bX cX) = R1C (Right aX) (Right bX) cX

--------------------------------------------------------------------------------

data ExecError n
  = ExecOutputVarsNotMappedError [Var] (IntMap n)
  | ExecOutputError [n] [n]
  | ExecR1CUnsatisfiableError [R1C n] (IntMap n)
  | ExecInputUnmatchedError Int Int
  | ExecVarUnassignedError [Var] (IntMap n)
  deriving (Eq, Generic, NFData, Functor)

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
    "expecting "
      ++ show expected
      ++ " input(s) but got "
      ++ show actual
      ++ " input(s)"
  show (ExecVarUnassignedError vars witness) =
    "these variables:\n "
      ++ show vars
      ++ "\n are not assigned in: \n"
      ++ showWitness (IntMap.restrictKeys witness (IntSet.fromList vars))
