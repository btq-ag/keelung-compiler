module Keelung.Compiler.R1CS where

import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Maybe (mapMaybe)
import Data.Semiring (Semiring (..))
import qualified Data.Set as Set
import Keelung.Compiler.Constraint
import Keelung.Compiler.Constraint.Polynomial (Poly)
import qualified Keelung.Compiler.Constraint.Polynomial as Poly
import Keelung.Compiler.Optimise (optimiseWithWitness)
import Keelung.Compiler.Util
import Keelung.Field (N (..))
import Keelung.Syntax (Var)

-- | Starting from an initial partial assignment, solve the
-- constraints and return the resulting complete assignment.
-- Return `Left String` if the constraints are unsolvable.
generateWitness ::
  (GaloisField n, Bounded n, Integral n) =>
  -- | Constraints to be solved
  ConstraintSystem n ->
  -- | Initial assignment
  Witness n ->
  -- | Resulting assignment
  Either (ExecError n) (Witness n)
generateWitness cs env =
  let cs' = renumberConstraints cs
      -- pinnedVars =
      --   IntSet.toList (csInputVars cs)
      --     ++ case csOutputVar cs of
      --       Nothing -> []
      --       Just v -> [v]
      variables = [0 .. IntSet.size (csVars cs) - 1]
      (witness, _) = optimiseWithWitness env cs'
   in if all (isMapped witness) variables
        then Right witness
        else Left $ ExecVarUnassignedError [x | x <- variables, not $ isMapped witness x] witness
  where
    -- ( "unassigned variables,\n  "
    --     ++ show [x | x <- variables, not $ isMapped witness x]
    --     ++ ",\n"
    --     ++ "in assignment context\n  "
    --     ++ show (fmap N witness)
    --     ++ ",\n"
    --     ++ "in pinned-variable context\n  "
    --     ++ show pinnedVars
    --     ++ ",\n"
    --     ++ "in reduced-constraint context\n  "
    --     ++ show cs''
    --     ++ ",\n"
    --     ++ "in constraint context\n  "
    --     ++ show cs'
    -- )

    isMapped witness var = IntMap.member var witness

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

-- | A Rank-1 Constraint is a relation between 3 polynomials
--      Ax * Bx = Cx
data R1C n = R1C (Either n (Poly n)) (Either n (Poly n)) (Either n (Poly n))
  deriving (Eq)

instance (Show n, Integral n, Bounded n, Fractional n) => Show (R1C n) where
  show (R1C aX bX cX) = case (aX, bX, cX) of
    (Left 0, _, _) -> "0 = " ++ showVec cX
    (_, Left 0, _) -> "0 = " ++ showVec cX
    (Left 1, _, _) -> showVec bX ++ " = " ++ showVec cX
    (_, Left 1, _) -> showVec aX ++ " = " ++ showVec cX
    (_, _, _) -> showVec aX ++ " * " ++ showVec bX ++ " = " ++ showVec cX
    where
      showVec (Left c) = show (N c)
      showVec (Right xs) = show xs

satisfyR1C :: GaloisField a => Witness a -> R1C a -> Bool
satisfyR1C witness constraint
  | R1C aV bV cV <- constraint =
    evaluate aV witness `times` evaluate bV witness == evaluate cV witness
  where
    evaluate :: GaloisField a => Either a (Poly a) -> Witness a -> a
    evaluate (Left x) _ = x
    evaluate (Right p) w = Poly.evaluate p w

--------------------------------------------------------------------------------

-- | Rank-1 Constraint Systems
data R1CS n = R1CS
  { r1csClauses :: [R1C n],
    r1csNumOfVars :: Int,
    r1csInputVars :: IntSet,
    r1csOutputVar :: Maybe Var,
    r1csWitnessGen :: Witness n -> Either (ExecError n) (Witness n)
  }

instance (Show n, Integral n, Bounded n, Fractional n) => Show (R1CS n) where
  show (R1CS cs n ivs ovs _) =
    "R1CS {\n\
    \  R1C clauses ("
      ++ show numberOfClauses
      ++ ")"
      ++ showClauses
      ++ "\n  number of variables: "
      ++ show n
      ++ "\n"
      ++ "  number of input vars: "
      ++ show (IntSet.size ivs)
      ++ "\n"
      ++ "  output var: "
      ++ show ovs
      ++ "\n"
      ++ "}"
    where
      numberOfClauses = length cs
      showClauses =
        if numberOfClauses > 30
          then "\n"
          else ":\n" ++ List.intercalate "\n" (map (\s -> "    " ++ show s) cs)

-- `Nothing` if all constraints are satisfiable
-- `Just [R1C]` if at least one constraint is unsatisfiable
satisfyR1CS :: GaloisField n => Witness n -> R1CS n -> Maybe [R1C n]
satisfyR1CS witness r1cs =
  let clauses = r1csClauses r1cs
      unsatisfiable = filter (not . satisfyR1C witness) clauses
   in if null unsatisfiable
        then Nothing
        else Just unsatisfiable

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
    toR1C (CAdd xs) =
      Just $
        R1C
          (Left 1)
          (Right xs)
          (Left 0)
    -- toR1C (CMul cx dy (e, Nothing)) =
    --   Just $
    --     R1C (uncurry (flip Poly.singleton) cx) (uncurry (flip Poly.singleton) dy) (Poly.build e mempty)
    -- toR1C (CMul cx dy (e, Just z)) =
    --   Just $
    --     R1C (uncurry (flip Poly.singleton) cx) (uncurry (flip Poly.singleton) dy) (uncurry (flip Poly.singleton) (e, z))
    toR1C (CMul2 aX bX cX) =
      Just $ R1C (Right aX) (Right bX) cX
    toR1C CNQZ {} = Nothing

witnessOfR1CS :: [n] -> R1CS n -> Either (ExecError n) (Witness n)
witnessOfR1CS inputs r1cs =
  let inputVars = r1csInputVars r1cs
   in if IntSet.size inputVars /= length inputs
        then Left $ ExecInputUnmatchedError (IntSet.size inputVars) (length inputs)
        else r1csWitnessGen r1cs $ IntMap.fromList (zip (IntSet.toList inputVars) inputs)

--------------------------------------------------------------------------------

data ExecError n
  = ExecOutputVarNotMappedError (Maybe Var) (IntMap n)
  | ExecOutputError (Maybe n) (Maybe n)
  | ExecR1CUnsatisfiableError [R1C n] (IntMap n)
  | ExecInputUnmatchedError Int Int
  | ExecVarUnassignedError [Var] (IntMap n)
  deriving (Eq)

instance (Show n, Bounded n, Integral n, Fractional n) => Show (ExecError n) where
  show (ExecOutputVarNotMappedError var witness) =
    "output variable "
      ++ show var
      ++ " is not mapped in\n  "
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

-- ( "unassigned variables,\n  "
--     ++ show [x | x <- variables, not $ isMapped witness x]
--     ++ ",\n"
--     ++ "in assignment context\n  "
--     ++ show (fmap N witness)
--     ++ ",\n"
--     ++ "in pinned-variable context\n  "
--     ++ show pinnedVars
--     ++ ",\n"
--     ++ "in reduced-constraint context\n  "
--     ++ show cs''
--     ++ ",\n"
--     ++ "in constraint context\n  "
--     ++ show cs'
-- )