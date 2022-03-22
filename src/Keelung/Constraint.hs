module Keelung.Constraint where

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
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
data Constraint n
  = CAdd !n !(CoeffMap n)
  | CMul !(n, Var) !(n, Var) !(n, Maybe Var)
  deriving (Eq)

instance (Show n, Eq n, Num n) => Show (Constraint n) where
  show (CAdd 0 m) = show m
  show (CAdd n m) = show n <> " + " <> show m
  show (CMul (a, x) (b, y) (c, z)) =
    let showTerm 1 var = "$" <> show var
        showTerm coeff var = show coeff <> "$" <> show var
     in showTerm a x <> " * " <> showTerm b y
          <> " = "
          <> case z of
            Nothing -> show c
            Just z' -> showTerm c z'

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

-- | Return the list of variables occurring in constraints
varsInConstraint :: Constraint a -> IntSet
varsInConstraint (CAdd _ m) = CoeffMap.keysSet m
varsInConstraint (CMul (_, x) (_, y) (_, Nothing)) = IntSet.fromList [x, y]
varsInConstraint (CMul (_, x) (_, y) (_, Just z)) = IntSet.fromList [x, y, z]

varsInConstraints :: Set (Constraint a) -> IntSet
varsInConstraints = IntSet.unions . map varsInConstraint . Set.toList

--------------------------------------------------------------------------------

-- | Constraint System
data ConstraintSystem n = ConstraintSystem
  { csConstraints :: Set (Constraint n),
    csNumberOfVars :: Int,
    csInputVars :: IntSet,
    csOutputVars :: IntSet
  }

instance (Show n, Bounded n, Integral n, Fractional n) => Show (ConstraintSystem n) where
  show (ConstraintSystem set numVars inputVars outputVars) =
    "ConstraintSystem {\n\
    \  number of constraints: "
      <> show (Set.size set)
      <> "\n"
      <> ( if Set.size set < 20
             then "  constraints:\n" <> printConstraints set <> "\n"
             else ""
         )
      <> "  number of variables: "
      <> show numVars
      <> "\n\
         \  number of input variables: "
      <> show (IntSet.size inputVars)
      <> "\n  output variables: "
      <> show (IntSet.toList outputVars)
      <> "\n\
         \}"
    where
      printConstraint :: (Show n, Bounded n, Fractional n, Integral n) => Constraint n -> String
      printConstraint (CAdd n xs) =
        "    " <> show (CAdd (DebugGF n) (fmap DebugGF xs))
      printConstraint (CMul (a, x) (b, y) (c, z)) =
        "    " <> show (CMul (DebugGF a, x) (DebugGF b, y) (DebugGF c, z))

      printConstraints :: (Show n, Bounded n, Fractional n, Integral n) => Set (Constraint n) -> String
      printConstraints = unlines . map printConstraint . Set.toList