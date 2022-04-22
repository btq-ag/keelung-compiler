{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Keelung.Constraint where

import Data.Field.Galois (GaloisField)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Keelung.Constraint.CoeffMap (CoeffMap)
import qualified Keelung.Constraint.CoeffMap as CoeffMap
import Keelung.Syntax.Common
import Keelung.Util (DebugGF (DebugGF))

--------------------------------------------------------------------------------

-- | Constraint
--      CAdd: 0 = c + c₀x₀ + c₁x₁ ... cₙxₙ
--      CMul: nx + by = c or nx + by = cz
--      CNQZ: if x == 0 then m = 0 else m = recip x
data Constraint n
  = CAdd !n !(CoeffMap n)
  | CMul !(n, Var) !(n, Var) !(n, Maybe Var)
  | CNQZ Var Var -- x & m
  deriving (Eq)

-- | Smart constructor for the CAdd constraint
cadd :: GaloisField n => n -> [(Var, n)] -> Constraint n
cadd !c !xs = CAdd c (CoeffMap.fromList xs)

instance (Show n, Eq n, Num n, Bounded n, Integral n, Fractional n) => Show (Constraint n) where
  show (CAdd 0 m) = show m
  show (CAdd n m) = show (DebugGF n) <> " + " <> show m
  show (CMul (a, x) (b, y) (c, z)) =
    let showTerm 1 var = "$" <> show var
        showTerm coeff var = show (DebugGF coeff) <> "$" <> show var
     in showTerm a x <> " * " <> showTerm b y
          <> " = "
          <> case z of
            Nothing -> show $ DebugGF c
            Just z' -> showTerm c z'
  show (CNQZ x m) = "CNQZ $" <> show x <> " $" <> show m

instance Ord n => Ord (Constraint n) where
  {-# SPECIALIZE instance Ord (Constraint GF181) #-}
  compare CMul {} CAdd {} = GT
  compare CAdd {} CMul {} = LT
  compare (CAdd c m) (CAdd c' m') =
    -- perform lexicographical comparison with tuples
    compare (c, m) (c', m')
  compare (CMul (a, x) (b, y) (c, z)) (CMul (a', x') (b', y') (c', z')) =
    -- perform lexicographical comparison with tuples
    compare (x, y, z, a, b, c) (x', y', z', a', b', c')
  compare CNQZ {} CNQZ {} = EQ
  compare CNQZ {} _ = LT
  compare _ CNQZ {} = GT

--------------------------------------------------------------------------------

-- | Return the list of variables occurring in constraints
varsInConstraint :: Constraint a -> IntSet
varsInConstraint (CAdd _ m) = CoeffMap.keysSet m
varsInConstraint (CMul (_, x) (_, y) (_, Nothing)) = IntSet.fromList [x, y]
varsInConstraint (CMul (_, x) (_, y) (_, Just z)) = IntSet.fromList [x, y, z]
varsInConstraint (CNQZ x y) = IntSet.fromList [x, y]

varsInConstraints :: Set (Constraint a) -> IntSet
varsInConstraints = IntSet.unions . Set.map varsInConstraint

--------------------------------------------------------------------------------

-- | Constraint System
data ConstraintSystem n = ConstraintSystem
  { csConstraints :: !(Set (Constraint n)),
    csBooleanInputVarConstraints :: ![Constraint n],
    csNumOfVars :: !Int,
    csInputVars :: !IntSet,
    -- csBooleanInputVars :: !IntSet,
    csOutputVar :: !(Maybe Var)
  }

-- | return the number of constraints (including constraints of boolean input vars)
numberOfConstraints :: ConstraintSystem n -> Int
numberOfConstraints (ConstraintSystem cs cs' _ _ _) = Set.size cs + length cs'

instance (Show n, Bounded n, Integral n, Fractional n) => Show (ConstraintSystem n) where
  show (ConstraintSystem set _ numOfVars inputVars outputVar) =
    "ConstraintSystem {\n\
    \  number of constraints: "
      <> show (Set.size set)
      <> "\n"
      <> ( if Set.size set < 20
             then "  constraints:\n" <> printConstraints set <> "\n"
             else ""
         )
      <> "  number of variables: "
      <> show numOfVars
      <> "\n\
         \  number of input variables: "
      <> show (IntSet.size inputVars)
      <> "\n  output variable: $"
      <> show outputVar
      <> "\n\
         \}"
    where
      printConstraints :: (Show n, Bounded n, Fractional n, Integral n) => Set (Constraint n) -> String
      printConstraints = unlines . map (\c -> "    " <> show c) . Set.toList

-- | Sequentially renumber term variables '0..max_var'.  Return
--   renumbered constraints, together with the total number of
--   variables in the (renumbered) constraint set and the (possibly
--   renumbered) in and out variables.
renumberConstraints :: Ord n => ConstraintSystem n -> ConstraintSystem n
renumberConstraints cs =
  ConstraintSystem
    (Set.map renumberConstraint (csConstraints cs))
    (map renumberConstraint (csBooleanInputVarConstraints cs))
    (Map.size variableMap)
    (IntSet.map renumber (csInputVars cs))
    (renumber <$> csOutputVar cs)
  where
    -- mapping of old variable indices to new variable indices
    -- input variables are placed in the front
    variableMap = Map.fromList $ zip (inputVars ++ otherVars) [0 ..]
      where
        inputVars = IntSet.toList (csInputVars cs)
        otherVars = filter isNotInput $ IntSet.toList $ varsInConstraints $ csConstraints cs
        isNotInput = not . flip IntSet.member (csInputVars cs)

    renumber var = case Map.lookup var variableMap of
      Nothing ->
        error
          ( "can't find a binding for variable " ++ show var
              ++ " in map "
              ++ show variableMap
          )
      Just var' -> var'

    renumberConstraint constraint = case constraint of
      CAdd a m ->
        CAdd a $ CoeffMap.mapKeys renumber m
      CMul (a, x) (b, y) (c, z) ->
        CMul (a, renumber x) (b, renumber y) (c, renumber <$> z)
      CNQZ x y ->
        CNQZ (renumber x) (renumber y)
