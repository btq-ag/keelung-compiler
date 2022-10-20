--------------------------------------------------------------------------------
--  Constraint Set Minimisation
--------------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}

module Keelung.Compiler.Optimize where

import Control.Arrow (left)
import Data.Field.Galois (GaloisField)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Keelung (Elaborable, elaborate)
import Keelung.Compiler.Constraint
import qualified Keelung.Compiler.Optimize.MinimizeConstraints as MinimizeConstraints
import qualified Keelung.Compiler.Optimize.MinimizeConstraints2 as MinimizeConstraints2
import Keelung.Compiler.Optimize.Monad
import qualified Keelung.Compiler.Optimize.Rewriting as Rewriting
import Keelung.Compiler.Syntax.Untyped (TypeErased (..))
import Keelung.Compiler.Util (Witness)
import Keelung.Monad
import qualified Keelung.Syntax.Typed as C

import Keelung.Syntax.VarCounters
--------------------------------------------------------------------------------

elaborateAndRewrite :: Elaborable t => Comp t -> Either String C.Elaborated
elaborateAndRewrite prog = left show (elaborate prog >>= Rewriting.run)

optimizeWithWitness :: (GaloisField n, Integral n) => Witness n -> ConstraintSystem n -> (Witness n, ConstraintSystem n)
optimizeWithWitness witness cs =
  -- NOTE: Pinned vars include:
  --   - input vars
  --   - output vars
  -- Pinned vars are never optimized away.

  let pinnedVars = IntSet.fromDistinctAscList [0 .. pinnedVarSize (csVarCounters cs) - 1]
   in runOptiM witness $ do
        constraints <- MinimizeConstraints.run (IntSet.toList pinnedVars) (csConstraints cs)
        witness' <- witnessOfVars [0 .. totalVarSize (csVarCounters cs) - 1]

        return (witness', renumberConstraints $ cs {csConstraints = constraints})

optimizeWithInput :: (GaloisField n, Integral n) => [n] -> ConstraintSystem n -> (Witness n, ConstraintSystem n)
optimizeWithInput ins cs =
  let witness = IntMap.fromList (zip [0 .. inputVarSize (csVarCounters cs) - 1] ins)
   in optimizeWithWitness witness cs

optimize1 :: (GaloisField n, Integral n) => ConstraintSystem n -> ConstraintSystem n
optimize1 = snd . optimizeWithInput mempty

optimize2 :: GaloisField n => ConstraintSystem n -> ConstraintSystem n
optimize2 cs =
  -- NOTE: Pinned vars include:
  --   - input vars
  --   - output vars
  -- Pinned vars are never optimized away.
  let pinnedVars = IntSet.fromDistinctAscList [0 .. pinnedVarSize (csVarCounters cs) - 1]
      constraints = MinimizeConstraints2.run pinnedVars (csConstraints cs)
   in renumberConstraints $ cs {csConstraints = constraints}

--------------------------------------------------------------------------------

-- | Result of optimisation
data Result = Result
  { -- | The number of constraints that have been optimized away
    resultConstraintReduction :: Int,
    -- | The number of variables that have been optimized away
    resultVariableReduction :: Int,
    -- | The number of assignments that have been optimized away
    resultAssignmentReduction :: Int
  }
  deriving (Eq, Ord, Show)

compareTypeErased :: TypeErased n -> TypeErased n -> Result
compareTypeErased x y =
  Result
    { resultConstraintReduction = 0,
      resultVariableReduction = totalVarSize (erasedVarCounters x) - totalVarSize (erasedVarCounters y),
      resultAssignmentReduction = length (erasedAssignments x) - length (erasedAssignments y)
    }
