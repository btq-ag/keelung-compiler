module Keelung.R1CS where

import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Maybe (mapMaybe)
import Data.Semiring (Semiring (..))
import qualified Data.Set as Set
import Keelung.Constraint
import qualified Keelung.Constraint.CoeffMap as CoeffMap
import Keelung.Optimise (optimise, optimiseWithWitness)
import Keelung.Syntax.Common
import Keelung.Util

-- | Starting from an initial partial assignment, solve the
-- constraints and return the resulting complete assignment.
-- Return `Left String` if the constraints are unsolvable.
generateWitness ::
  (GaloisField a, Bounded a, Integral a) =>
  -- | Constraints to be solved
  ConstraintSystem a ->
  -- | Initial assignment
  Witness a ->
  -- | Resulting assignment
  Either String (Witness a)
generateWitness cs env =
  let pinnedVars =
        IntSet.toList (csInputVars cs)
          ++ case csOutputVar cs of
            Nothing -> []
            Just v -> [v]
      variables = [0 .. csNumOfVars cs - 1]
      (witness, cs') = optimiseWithWitness env cs
   in if all (isMapped witness) variables
        then Right witness
        else
          Left
            ( "unassigned variables,\n  "
                ++ show [x | x <- variables, not $ isMapped witness x]
                ++ ",\n"
                ++ "in assignment context\n  "
                ++ show (fmap DebugGF witness)
                ++ ",\n"
                ++ "in pinned-variable context\n  "
                ++ show pinnedVars
                ++ ",\n"
                ++ "in reduced-constraint context\n  "
                ++ show cs'
                ++ ",\n"
                ++ "in constraint context\n  "
                ++ show cs
            )
  where
    isMapped witness var = IntMap.member var witness

--------------------------------------------------------------------------------

-- A Polynomial is a mapping from variables to their coefficients
type Poly n = IntMap n

-- | The constant polynomial equal 'c'
constPoly :: a -> Poly a
constPoly c = IntMap.insert (-1) c IntMap.empty

-- | The polynomial equal variable 'x'
varPoly :: (a, Var) -> Poly a
varPoly (coeff, x) = IntMap.insert x coeff IntMap.empty

--------------------------------------------------------------------------------

-- | A Rank-1 Constraint is a relation between 3 polynomials
--      Ax * Bx = Cx
data R1C n = R1C (Poly n) (Poly n) (Poly n)

instance Show n => Show (R1C n) where
  show (R1C aV bV cV) = show aV ++ "*" ++ show bV ++ "==" ++ show cV

satisfyR1C :: GaloisField a => Witness a -> R1C a -> Bool
satisfyR1C witness constraint
  | R1C aV bV cV <- constraint =
    inner aV witness `times` inner bV witness == inner cV witness
  where
    inner :: GaloisField a => Poly a -> Witness a -> a
    inner polynoomial w =
      IntMap.foldlWithKey
        (\acc k v -> (v `times` IntMap.findWithDefault zero k w) `plus` acc)
        (IntMap.findWithDefault zero (-1) polynoomial)
        polynoomial

--------------------------------------------------------------------------------

-- | Rank-1 Constraint Systems
data R1CS n = R1CS
  { r1csClauses :: [R1C n],
    r1csNumOfVars :: Int,
    r1csInputVars :: IntSet,
    r1csOutputVar :: Maybe Var,
    r1csWitnessGen :: Witness n -> Either String (Witness n)
  }

instance Show n => Show (R1CS n) where
  show (R1CS cs nvs ivs ovs _) = show (cs, nvs, ivs, ovs)

satisfyR1CS :: GaloisField n => Witness n -> R1CS n -> Bool
satisfyR1CS witness = all (satisfyR1C witness) . r1csClauses

fromConstraintSystem :: (GaloisField n, Bounded n, Integral n) => ConstraintSystem n -> R1CS n
fromConstraintSystem cs =
  let cs' = optimise cs
   in R1CS
        (mapMaybe toR1C (Set.toList (csConstraints cs') ++ csBooleanInputVarConstraints cs'))
        (csNumOfVars cs')
        (csInputVars cs')
        (csOutputVar cs')
        (generateWitness cs')
  where
    toR1C :: GaloisField n => Constraint n -> Maybe (R1C n)
    toR1C (CAdd a m) =
      Just $
        R1C
          (constPoly one)
          (CoeffMap.toIntMap $ CoeffMap.insert (-1) a m)
          (constPoly zero)
    toR1C (CMul cx dy (e, Nothing)) =
      Just $
        R1C (varPoly cx) (varPoly dy) (constPoly e)
    toR1C (CMul cx dy (e, Just z)) =
      Just $
        R1C (varPoly cx) (varPoly dy) (varPoly (e, z))
    toR1C CNQZ {} = Nothing

witnessOfR1CS :: [n] -> R1CS n -> Either String (Witness n)
witnessOfR1CS inputs r1cs =
  let inputVars = r1csInputVars r1cs
   in if IntSet.size inputVars /= length inputs
        then
          Left
            ( "expected "
                ++ show (IntSet.size inputVars)
                ++ " input(s)"
                ++ " but got "
                ++ show (length inputs)
                ++ " input(s)"
            )
        else r1csWitnessGen r1cs $ IntMap.fromList (zip (IntSet.toList inputVars) inputs)