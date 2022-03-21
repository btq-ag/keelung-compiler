module Keelung.R1CS where

import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Semiring (Semiring (..))
import Keelung.Syntax.Common

-- -- | Starting from an initial partial assignment [env], solve the
-- -- constraints [cs] and return the resulting complete assignment.
-- -- If the constraints are unsolvable from [env], report the first
-- -- constraint that is violated (under normal operation, this error
-- -- case should NOT occur).
-- generateWitness ::
--   (GaloisField a, Bounded a, Integral a) =>
--   -- | Constraints to be solved
--   ConstraintSystem a ->
--   -- | Initial assignment
--   IntMap a ->
--   -- | Resulting assignment
--   Witness a
-- generateWitness cs env =
--   let pinnedVars = csInputVars cs <> csOutputVars cs
--       variables = [0 .. csNumberOfVars cs - 1]
--       (assgn, cs') = simplifyConstrantSystem True env cs
--    in if all_assigned variables assgn
--         then assgn
--         else
--           fail_with $
--             ErrMsg
--               ( "unassigned variables,\n  "
--                   ++ show (unassigned variables assgn)
--                   ++ ",\n"
--                   ++ "in assignment context\n  "
--                   ++ show assgn
--                   ++ ",\n"
--                   ++ "in pinned-variable context\n  "
--                   ++ show pinnedVars
--                   ++ ",\n"
--                   ++ "in reduced-constraint context\n  "
--                   ++ show cs'
--                   ++ ",\n"
--                   ++ "in constraint context\n  "
--                   ++ show cs
--               )
--   where
--     all_assigned vars0 assgn = all (is_mapped assgn) vars0
--     is_mapped assgn x = isJust (IntMap.lookup x assgn)
--     unassigned vars0 assgn = [x | x <- vars0, not $ is_mapped assgn x]

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
    r1csNumVars :: Int,
    r1csInputVars :: [Var],
    r1csOutputVars :: [Var],
    r1csWitnessGen :: Witness n -> Witness n
  }

instance Show n => Show (R1CS n) where
  show (R1CS cs nvs ivs ovs _) = show (cs, nvs, ivs, ovs)

satisfyR1CS :: GaloisField a => Witness a -> R1CS a -> Bool
satisfyR1CS witness = all (satisfyR1C witness) . r1csClauses

-- fromConstraintSystem :: GaloisField a => ConstraintSystem a -> (Witness a -> Witness a) -> R1CS a
-- fromConstraintSystem cs =
--   R1CS
--     (Set.foldr go [] (cs_constraints cs))
--     (cs_num_vars cs)
--     (cs_in_vars cs)
--     (cs_out_vars cs)
--   where
--     go (CAdd a m) xs =
--       R1C
--         (constPoly one)
--         (Poly $ CoeffMap.toIntMap $ CoeffMap.insert (-1) a m)
--         (constPoly zero) :
--       xs
--     go (CMult cx dy (e, Nothing)) xs =
--       R1C (varPoly cx) (varPoly dy) (constPoly e) : xs
--     go (CMult cx dy (e, Just z)) xs =
--       R1C (varPoly cx) (varPoly dy) (varPoly (e, z)) : xs
--     go CMagic {} xs = xs
