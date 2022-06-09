{-# OPTIONS_GHC -Wno-type-defaults #-}

module Keelung.Compiler.Constraint2 where

import Data.Foldable (toList)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Keelung.Compiler.Constraint.Polynomial as Poly
import Keelung.Syntax (Var)
import Keelung.Compiler.Constraint (Constraint(..), varsInConstraints)
import Keelung.Field

--------------------------------------------------------------------------------

-- | Constraint System
data ConstraintSystem = ConstraintSystem
  { csConstraints :: !(Set (Constraint Integer)),
    csBooleanInputVarConstraints :: ![Constraint Integer],
    csVars :: !IntSet,
    csInputVars :: !IntSet,
    csOutputVar :: !(Maybe Var),
    csFieldType :: !FieldType
  }
  deriving (Eq)

-- | return the number of constraints (including constraints of boolean input vars)
numberOfConstraints :: ConstraintSystem -> Int
numberOfConstraints (ConstraintSystem cs cs' _ _ _ _) = Set.size cs + length cs'

instance Show ConstraintSystem where
  show (ConstraintSystem constraints boolConstraints vars inputVars outputVar fieldType) =
    "ConstraintSystem {\n\
    \  constraints ("
      <> show (length constraints)
      <> ")"
      <> ( if True -- Set.size constraints < 30
             then ":\n  \n" <> printConstraints (toList constraints) <> "\n"
             else "\n"
         )
      <> "  boolean constraints ("
      <> show (length boolConstraints)
      <> ")"
      <> ( if True
             then ":\n  \n" <> printConstraints boolConstraints <> "\n"
             else "\n"
         )
      <> "  number of variables: "
      <> show (IntSet.size vars)
      <> "\n\
         \  number of input variables: "
      <> show (IntSet.size inputVars)
      <> ":\n    "
      <> show (IntSet.toList inputVars)
      <> "\n"
      -- <> ( if IntSet.size inputVars < 20
      --        then ":\n    " <> show (IntSet.toList inputVars) <> "\n"
      --        else "\n"
      --    )
      <> "\n  output variable: $"
      <> show outputVar
      <> "\n\
         \}"
    where
      printConstraints :: [Constraint Integer] -> String
      printConstraints xs = unlines $ map (\c -> "    " <> show (fmap (normalize fieldType) c)) xs

-- | Sequentially renumber term variables '0..max_var'.  Return
--   renumbered constraints, together with the total number of
--   variables in the (renumbered) constraint set and the (possibly
--   renumbered) in and out variables.
renumberConstraints :: ConstraintSystem -> ConstraintSystem
renumberConstraints cs =
  ConstraintSystem
    (Set.map renumberConstraint (csConstraints cs))
    (map renumberConstraint (csBooleanInputVarConstraints cs))
    (IntSet.fromList renumberedVars)
    (IntSet.map renumber (csInputVars cs))
    (renumber <$> csOutputVar cs)
    (csFieldType cs)
  where
    -- variables in constraints (that should be kept after renumbering!)
    vars = varsInConstraints (csConstraints cs)

    -- variables after renumbering (should have the same size as `vars`)
    renumberedVars = [0 .. IntSet.size vars - 1]

    -- mapping of old variables to new variables
    -- input variables are placed in the front
    variableMap = Map.fromList $ zip vars' renumberedVars
      where
        otherVars = IntSet.difference vars (csInputVars cs)
        vars' = IntSet.toList (csInputVars cs) ++ IntSet.toList otherVars

    renumber var = case Map.lookup var variableMap of
      Nothing ->
        error
          ( "can't find a binding for variable " ++ show var
              ++ " in map "
              ++ show variableMap
          )
      Just var' -> var'

    renumberConstraint constraint = case constraint of
      CAdd xs ->
        CAdd $ Poly.mapVars renumber xs
      CMul2 aV bV cV ->
        CMul2 (Poly.mapVars renumber aV) (Poly.mapVars renumber bV) (Poly.mapVars renumber <$> cV)
      CNQZ x y ->
        CNQZ (renumber x) (renumber y)
