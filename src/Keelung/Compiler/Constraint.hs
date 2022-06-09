{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Keelung.Compiler.Constraint where

import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Keelung.Compiler.Constraint.Polynomial (Poly)
import qualified Keelung.Compiler.Constraint.Polynomial as Poly
import Keelung.Field
import Keelung.Syntax (Var)

--------------------------------------------------------------------------------

-- | Constraint
--      CAdd: 0 = c + c₀x₀ + c₁x₁ ... cₙxₙ
--      CMul: ax * by = c or ax * by = cz
--      CNQZ: if x == 0 then m = 0 else m = recip x
data Constraint n
  = CAdd !(Poly n)
  | CMul2 !(Poly n) !(Poly n) !(Either n (Poly n))
  | CNQZ Var Var -- x & m

instance (Eq n, Num n) => Eq (Constraint n) where
  xs == ys = case (xs, ys) of
    (CAdd x, CAdd y) -> x == y
    (CMul2 x y z, CMul2 u v w) ->
      ((x == u && y == v) || (x == v && y == u)) && z == w
    (CNQZ x y, CNQZ u v) -> x == u && y == v
    _ -> False

instance Functor Constraint where
  fmap f (CAdd x) = CAdd (fmap f x)
  fmap f (CMul2 x y (Left z)) = CMul2 (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMul2 x y (Right z)) = CMul2 (fmap f x) (fmap f y) (Right (fmap f z))
  fmap _ (CNQZ x y) = CNQZ x y

-- | Smart constructor for the CAdd constraint
cadd :: GaloisField n => n -> [(Var, n)] -> Constraint n
cadd !c !xs = CAdd $ Poly.build c xs

cmul :: GaloisField n => Var -> Var -> (n, [(Var, n)]) -> Constraint n
cmul !x !y (c, zs) = CMul2 (Poly.singleton x 1) (Poly.singleton y 1) (Poly.buildEither c zs)

instance (Show n, Eq n, Num n, Bounded n, Integral n, Fractional n) => Show (Constraint n) where
  show (CAdd xs) = "A " ++ show xs ++ " = 0"
  show (CMul2 aV bV cV) = "M " ++ showPoly aV <> " * " <> showPoly bV <> " = " <> showPoly' cV
    where
      showPoly poly =
        if IntMap.size (Poly.coeffs poly) > 1
          then "(" <> show poly <> ")"
          else show poly
      showPoly' (Left x) = show (N x)
      showPoly' (Right poly) =
        if IntMap.size (Poly.coeffs poly) > 1
          then "(" <> show poly <> ")"
          else show poly
  show (CNQZ x m) = "Q $" <> show x <> " $" <> show m

instance (Ord n, Num n) => Ord (Constraint n) where
  {-# SPECIALIZE instance Ord (Constraint GF181) #-}
  compare (CMul2 aV bV cV) (CMul2 aX bX cX) = compare (aV, bV, cV) (aX, bX, cX)
  compare _ CMul2 {} = LT -- CMul2 is always greater than anything
  compare CMul2 {} _ = GT
  -- compare CMul {} CAdd {} = GT
  -- compare CAdd {} CMul {} = LT
  compare (CAdd xs) (CAdd ys) =
    if xs == ys then EQ else compare xs ys
  -- compare (CMul (a, x) (b, y) (c, z)) (CMul (a', x') (b', y') (c', z')) =
  -- perform lexicographical comparison with tuples
  -- compare (x, y, z, a, b, c) (x', y', z', a', b', c')
  compare CNQZ {} CNQZ {} = EQ
  compare CNQZ {} _ = LT
  compare _ CNQZ {} = GT

--------------------------------------------------------------------------------

-- | Return the list of variables occurring in constraints
varsInConstraint :: Constraint a -> IntSet
varsInConstraint (CAdd xs) = Poly.vars xs
-- varsInConstraint (CMul (_, x) (_, y) (_, Nothing)) = IntSet.fromList [x, y]
-- varsInConstraint (CMul (_, x) (_, y) (_, Just z)) = IntSet.fromList [x, y, z]
varsInConstraint (CMul2 aV bV (Left _)) = IntSet.unions $ map Poly.vars [aV, bV]
varsInConstraint (CMul2 aV bV (Right cV)) = IntSet.unions $ map Poly.vars [aV, bV, cV]
varsInConstraint (CNQZ x y) = IntSet.fromList [x, y]

varsInConstraints :: Set (Constraint a) -> IntSet
varsInConstraints = IntSet.unions . Set.map varsInConstraint

--------------------------------------------------------------------------------

-- | Constraint System
data ConstraintSystem n = ConstraintSystem
  { csConstraints :: !(Set (Constraint n)),
    csBooleanInputVarConstraints :: ![Constraint n],
    csVars :: !IntSet,
    csInputVars :: !IntSet,
    csOutputVar :: !(Maybe Var)
  }
  deriving (Eq)

-- | return the number of constraints (including constraints of boolean input vars)
numberOfConstraints :: ConstraintSystem n -> Int
numberOfConstraints (ConstraintSystem cs cs' _ _ _) = Set.size cs + length cs'

instance (Show n, Bounded n, Integral n, Fractional n) => Show (ConstraintSystem n) where
  show (ConstraintSystem constraints boolConstraints vars inputVars outputVar) =
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
      printConstraints = unlines . map (\c -> "    " <> show c)

-- | Sequentially renumber term variables '0..max_var'.  Return
--   renumbered constraints, together with the total number of
--   variables in the (renumbered) constraint set and the (possibly
--   renumbered) in and out variables.
renumberConstraints :: (Ord n, Num n) => ConstraintSystem n -> ConstraintSystem n
renumberConstraints cs =
  ConstraintSystem
    (Set.map renumberConstraint (csConstraints cs))
    (map renumberConstraint (csBooleanInputVarConstraints cs))
    (IntSet.fromList renumberedVars)
    (IntSet.map renumber (csInputVars cs))
    (renumber <$> csOutputVar cs)
  where
    -- variables in constraints (that should be kept after renumbering!)
    vars = varsInConstraints (csConstraints cs)

    -- new variables after renumbering
    -- invariant: size == |vars in constraints| `max` |input vars|
    renumberedVars = [0 .. (IntSet.size vars `max` IntSet.size (csInputVars cs)) - 1]

    -- mapping of old variables to new variables
    -- input variables are placed in the front
    variableMap = Map.fromList $ zip oldVars renumberedVars
      where
        otherVars = IntSet.difference vars (csInputVars cs)
        oldVars = IntSet.toList (csInputVars cs) ++ IntSet.toList otherVars

    renumber var = case Map.lookup var variableMap of
      Nothing ->
        error
          ( "can't find a binding for variable " ++ show var
              ++ " in map "
              ++ show variableMap
              ++ " test:\n"
              ++ show
                ( length $ csConstraints cs,
                  IntSet.toList $ varsInConstraints (csConstraints cs),
                  IntSet.toList vars,
                  IntSet.toList (csInputVars cs),
                  renumberedVars
                )
          )
      Just var' -> var'

    renumberConstraint constraint = case constraint of
      CAdd xs ->
        CAdd $ Poly.mapVars renumber xs
      CMul2 aV bV cV ->
        CMul2 (Poly.mapVars renumber aV) (Poly.mapVars renumber bV) (Poly.mapVars renumber <$> cV)
      CNQZ x y ->
        CNQZ (renumber x) (renumber y)
