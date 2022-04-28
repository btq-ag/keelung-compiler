module Keelung.R1CS where

import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Maybe (mapMaybe)
import Data.Semiring (Semiring (..))
import qualified Data.Set as Set
import Keelung.Constraint
import qualified Keelung.Constraint.CoeffMap as CoeffMap
import Keelung.Optimise (optimiseWithWitness)
import Keelung.Syntax.Common
import Keelung.Util

-- import qualified Data.List as List

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
      variables = [0 .. IntSet.size (csVars cs) - 1]
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
data Poly n
  = Poly n (IntMap n) -- the first field `n` is the constant term

-- Helper function for printing polynomials
--    empty polynomial is printed as ""
--    variables are prefixed with "$"
showPolynomial :: (Integral n, Show n, Bounded n, Fractional n) => IntMap n -> String
showPolynomial poly = go (IntMap.toList poly)
  where
    go [] = ""
    go [term] = printTerm term
    go (term : xs) = printTerm term ++ " + " ++ go xs

    printTerm (x, 1) = "$" ++ show x
    printTerm (x, -1) = "-$" ++ show x
    printTerm (x, c) = show (DebugGF c) ++ "$" ++ show x

constantOnly :: Poly n -> Maybe n
constantOnly (Poly c xs) = if IntMap.null xs then Just c else Nothing

instance (Show n, Integral n, Bounded n, Fractional n) => Show (Poly n) where
  show (Poly n poly) = case (n, IntMap.size poly) of
    (0, 0) -> "0"
    (0, _) -> showPolynomial poly
    (_, 0) -> show (DebugGF n)
    (_, _) -> show (DebugGF n) ++ " + " ++ showPolynomial poly

varPoly :: Semiring a => (a, Var) -> Poly a
varPoly (coeff, x) = Poly zero (IntMap.insert x coeff IntMap.empty)

--------------------------------------------------------------------------------

-- | A Rank-1 Constraint is a relation between 3 polynomials
--      Ax * Bx = Cx
data R1C n = R1C (Poly n) (Poly n) (Poly n)

instance (Show n, Integral n, Bounded n, Fractional n) => Show (R1C n) where
  show (R1C aX bX cX) = case (constantOnly aX, constantOnly bX, constantOnly cX) of
    (Just 0, _, _) -> "0 = " ++ show cX
    (_, Just 0, _) -> "0 = " ++ show cX
    (Just 1, _, _) -> show bX ++ " = " ++ show cX
    (_, Just 1, _) -> show aX ++ " = " ++ show cX
    (_, _, _) -> show aX ++ " * " ++ show bX ++ " = " ++ show cX

satisfyR1C :: GaloisField a => Witness a -> R1C a -> Bool
satisfyR1C witness constraint
  | R1C aV bV cV <- constraint =
    inner aV witness `times` inner bV witness == inner cV witness
  where
    inner :: GaloisField a => Poly a -> Witness a -> a
    inner (Poly n poly) w =
      IntMap.foldlWithKey
        (\acc k v -> (v `times` IntMap.findWithDefault zero k w) `plus` acc)
        n
        poly

--------------------------------------------------------------------------------

-- | Rank-1 Constraint Systems
data R1CS n = R1CS
  { r1csClauses :: [R1C n],
    r1csNumOfVars :: Int,
    r1csInputVars :: IntSet,
    r1csOutputVar :: Maybe Var,
    r1csWitnessGen :: Witness n -> Either String (Witness n)
  }

instance (Show n, Integral n, Bounded n, Fractional n) => Show (R1CS n) where
  show (R1CS cs n ivs ovs _) =
    "R1CS {\n\
    \  R1C clauses ("
      ++ show numberOfClauses
      ++ ")"
      ++ showClauses
      ++ "\n  number of variables: " ++ show n  ++ "\n"
      ++ "  number of input vars: " ++ show (IntSet.size ivs) ++ "\n"
      ++ "  output var: " ++ show ovs ++ "\n"
      ++ "}"
    where
      numberOfClauses = length cs
      showClauses =
        if numberOfClauses > 30
          then "\n"
          else ":\n" ++ List.intercalate "\n" (map (\s -> "    " ++ show s) cs)

satisfyR1CS :: GaloisField n => Witness n -> R1CS n -> Bool
satisfyR1CS witness = all (satisfyR1C witness) . r1csClauses

toR1CS :: (GaloisField n, Bounded n, Integral n) => ConstraintSystem n -> R1CS n
toR1CS cs =
  R1CS
    (mapMaybe toR1C (Set.toList (csConstraints cs) ++ csBooleanInputVarConstraints cs))
    (IntSet.size (csVars cs))
    (csInputVars cs)
    (csOutputVar cs)
    (generateWitness cs)
  where
    toR1C :: GaloisField n => Constraint n -> Maybe (R1C n)
    toR1C (CAdd a m) =
      Just $
        R1C
          (Poly one mempty)
          (Poly a (CoeffMap.toIntMap m))
          (Poly zero mempty)
    toR1C (CMul cx dy (e, Nothing)) =
      Just $
        R1C (varPoly cx) (varPoly dy) (Poly e mempty)
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