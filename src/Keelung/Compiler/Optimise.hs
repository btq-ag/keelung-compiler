--------------------------------------------------------------------------------
--  Constraint Set Minimisation
--------------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}

module Keelung.Compiler.Optimise where

import Data.Field.Galois (GaloisField)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Keelung.Compiler.Constraint
import Keelung.Monad
import qualified Keelung.Compiler.Optimise.MinimiseConstraints as MinimiseConstraints
import qualified Keelung.Compiler.Optimise.MinimiseConstraints2 as MinimiseConstraints2
import Keelung.Compiler.Optimise.Monad
import Keelung.Syntax
import Keelung (elaborateAndFlatten)
import Keelung.Compiler.Syntax.Untyped (TypeErased (..))
import Keelung.Compiler.Util (Witness)
import qualified Keelung.Syntax.Concrete as C
import qualified Keelung.Compiler.Optimise.Rewriting as Rewriting2
import Data.Typeable (Typeable)
import Keelung.Field

--------------------------------------------------------------------------------

elaborateAndRewrite :: (Typeable kind, Integral n, AcceptedField n) => Comp n (Expr kind n) -> Either String C.Elaborated
elaborateAndRewrite prog = elaborateAndFlatten prog >>= Rewriting2.run

optimiseWithWitness :: (GaloisField n, Bounded n, Integral n) => Witness n -> ConstraintSystem n -> (Witness n, ConstraintSystem n)
optimiseWithWitness witness cs =
  -- NOTE: Pinned vars include:
  --   - input vars
  --   - output vars
  -- Pinned vars are never optimised away.

  let pinnedVars = case csOutputVar cs of
        Nothing -> csInputVars cs
        Just outputVar -> IntSet.insert outputVar (csInputVars cs)
   in runOptiM witness $ do
        constraints <- MinimiseConstraints.run (IntSet.toList pinnedVars) (csConstraints cs)
        -- NOTE: In the next line, it's OK that 'pinnedVars'
        -- may overlap with 'constraintVars cs'.
        -- 'assignmentOfVars' might do a bit of duplicate
        -- work (to look up the same key more than once).
        assignments <- assignmentOfVars $ IntSet.toList $ pinnedVars <> csVars cs

        return (assignments, renumberConstraints $ cs {csConstraints = constraints})

optimiseWithInput :: (GaloisField n, Bounded n, Integral n) => [n] -> ConstraintSystem n -> (Witness n, ConstraintSystem n)
optimiseWithInput input cs =
  let witness = IntMap.fromList (zip (IntSet.toList (csInputVars cs)) input)
   in optimiseWithWitness witness cs

optimise :: (GaloisField n, Bounded n, Integral n) => ConstraintSystem n -> ConstraintSystem n
optimise = snd . optimiseWithInput mempty

optimise2 :: (GaloisField n, Bounded n, Integral n) => ConstraintSystem n -> ConstraintSystem n
optimise2 cs =
  -- NOTE: Pinned vars include:
  --   - input vars
  --   - output vars
  -- Pinned vars are never optimised away.
  let pinnedVars = case csOutputVar cs of
        Nothing -> csInputVars cs
        Just outputVar -> IntSet.insert outputVar (csInputVars cs)

      constraints = MinimiseConstraints2.run pinnedVars (csConstraints cs)
   in renumberConstraints $ cs {csConstraints = constraints}

--------------------------------------------------------------------------------

-- | Result of optimisation
data Result = Result
  { -- | The number of constraints that have been optimised away
    resultConstraintReduction :: Int,
    -- | The number of variables that have been optimised away
    resultVariableReduction :: Int,
    -- | The number of assignments that have been optimised away
    resultAssignmentReduction :: Int
  }
  deriving (Eq, Ord, Show)

compareTypeErased :: TypeErased n -> TypeErased n -> Result
compareTypeErased x y =
  Result
    { resultConstraintReduction = 0,
      resultVariableReduction = erasedNumOfVars x - erasedNumOfVars y,
      resultAssignmentReduction = length (erasedAssignments x) - length (erasedAssignments y)
    }
