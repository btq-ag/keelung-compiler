--------------------------------------------------------------------------------
--  Constraint Set Minimisation
--------------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}

module Keelung.Compiler.Optimize where

import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Keelung
import Keelung.Compiler.Compile.Error qualified as Compile
import Keelung.Compiler.ConstraintSystem (ConstraintSystem)
import Keelung.Compiler.Optimize.MinimizeConstraints qualified as MinimizeConstraints
import Keelung.Compiler.Optimize.MinimizeRelocatedConstraints qualified as MinimizeRelocatedConstraints
import Keelung.Compiler.Optimize.Monad
import Keelung.Compiler.Relocated
import Keelung.Compiler.Syntax.Internal (Internal (..))
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
        return (witness', renumberConstraints (cs {csConstraints = constraints}))

optimizeWithInput :: (GaloisField n, Integral n) => [n] -> RelocatedConstraintSystem n -> (Witness n, RelocatedConstraintSystem n)
optimizeWithInput inputs cs =
  let (start, end) = getPublicInputVarRange (csCounters cs)
      inputVars = [start .. end - 1]
      witness = IntMap.fromList (zip inputVars inputs)
   in optimizeWithWitness witness cs

optimizeOld :: (GaloisField n, Integral n) => RelocatedConstraintSystem n -> RelocatedConstraintSystem n
optimizeOld = snd . optimizeWithInput mempty

optimizeNew :: (GaloisField n, Integral n) => ConstraintSystem n -> Either (Compile.Error n) (ConstraintSystem n)
optimizeNew = MinimizeConstraints.run

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

compareInternal :: Internal n -> Internal n -> Result
compareInternal x y =
  Result
    { resultConstraintReduction = 0,
      resultVariableReduction = getTotalCount (internalCounters x) - getTotalCount (internalCounters y)
    }
