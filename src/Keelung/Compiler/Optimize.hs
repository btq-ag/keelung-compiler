--------------------------------------------------------------------------------
--  Constraint Set Minimisation
--------------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}

module Keelung.Compiler.Optimize where

import Data.Field.Galois (GaloisField)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Keelung.Compiler.Constraint (ConstraintSystem)
import qualified Keelung.Compiler.Optimize.MinimizeConstraints as MinimizeConstraints
import qualified Keelung.Compiler.Optimize.MinimizeRelocatedConstraints as MinimizeRelocatedConstraints
import qualified Keelung.Compiler.Optimize.MinimizeRelocatedConstraints2 as MinimizeRelocatedConstraints2
import Keelung.Compiler.Optimize.Monad
import Keelung.Compiler.Relocated
import Keelung.Compiler.Syntax.Untyped (TypeErased (..))
import Keelung.Compiler.Util (Witness)
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

optimizeWithWitness :: (GaloisField n, Integral n) => Witness n -> RelocatedConstraintSystem n -> (Witness n, RelocatedConstraintSystem n)
optimizeWithWitness witness cs =
  -- NOTE: Pinned vars include:
  --   - input vars
  --   - output vars
  -- Pinned vars are never optimized away.

  let counters = csCounters cs
      pinnedVarSize = getCountBySort OfPublicInput counters + getCountBySort OfPrivateInput counters + getCountBySort OfOutput counters
      pinnedVars = IntSet.fromDistinctAscList [0 .. pinnedVarSize - 1]
   in runOptiM witness $ do
        constraints <- MinimizeRelocatedConstraints.run counters (IntSet.toList pinnedVars) (csConstraints cs)
        witness' <- witnessOfVars [0 .. getTotalCount counters - 1]
        return (witness', renumberConstraints $ cs {csConstraints = constraints})

optimizeWithInput :: (GaloisField n, Integral n) => [n] -> RelocatedConstraintSystem n -> (Witness n, RelocatedConstraintSystem n)
optimizeWithInput inputs cs =
  let (start, end) = getPublicInputVarRange (csCounters cs)
      inputVars = [start .. end - 1]
      witness = IntMap.fromList (zip inputVars inputs)
   in optimizeWithWitness witness cs

optimize1 :: (GaloisField n, Integral n) => RelocatedConstraintSystem n -> RelocatedConstraintSystem n
optimize1 = snd . optimizeWithInput mempty

optimize1' :: (GaloisField n, Integral n) => ConstraintSystem n -> ConstraintSystem n
optimize1' = MinimizeConstraints.run

optimize2 :: (GaloisField n, Integral n) => RelocatedConstraintSystem n -> RelocatedConstraintSystem n
optimize2 rcs =
  -- NOTE: Pinned vars include:
  --   - input vars
  --   - output vars
  -- Pinned vars are never optimized away.
  let counters = csCounters rcs
      pinnedVarSize = getCountBySort OfPrivateInput counters + getCountBySort OfPublicInput counters + getCountBySort OfOutput counters
      -- pinnedVarSize = getCountBySort OfPublicInput counters + getCountBySort OfPrivateInput counters + getCountBySort OfOutput counters
      pinnedVars = IntSet.fromDistinctAscList [0 .. pinnedVarSize - 1]
      constraints = MinimizeRelocatedConstraints2.run pinnedVars (csConstraints rcs)
   in renumberConstraints $ rcs {csConstraints = constraints}

--------------------------------------------------------------------------------

-- | Result of optimisation
data Result = Result
  { -- | The number of constraints that have been optimized away
    resultConstraintReduction :: Int,
    -- | The number of variables that have been optimized away
    resultVariableReduction :: Int
    -- The number of assignments that have been optimized away
    -- resultAssignmentReduction :: Int
  }
  deriving (Eq, Ord, Show)

compareTypeErased :: TypeErased n -> TypeErased n -> Result
compareTypeErased x y =
  Result
    { resultConstraintReduction = 0,
      resultVariableReduction = getTotalCount (erasedCounters x) - getTotalCount (erasedCounters y)
      -- resultAssignmentReduction = length (erasedAssignments x) - length (erasedAssignments y)
    }
