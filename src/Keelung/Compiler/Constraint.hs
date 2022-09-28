{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Keelung.Compiler.Constraint where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Keelung.Constraint.Polynomial (Poly)
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Field
import Keelung.Types (Var)

--------------------------------------------------------------------------------

-- | Constraint
--      CAdd: 0 = c + c₀x₀ + c₁x₁ ... cₙxₙ
--      CMul: ax * by = c or ax * by = cz
--      CNQZ: if x == 0 then m = 0 else m = recip x
--      CXor: x ⊕ y = z
--      COr: x ∨ y = z
data Constraint n
  = CAdd !(Poly n)
  | CMul2 !(Poly n) !(Poly n) !(Either n (Poly n))
  | CNQZ Var Var -- x & m
  | CXor Var Var Var
  | COr Var Var Var
  deriving (Generic, NFData)

instance GaloisField n => Eq (Constraint n) where
  xs == ys = case (xs, ys) of
    (CAdd x, CAdd y) -> x == y
    (CMul2 x y z, CMul2 u v w) ->
      ((x == u && y == v) || (x == v && y == u)) && z == w
    (CNQZ x y, CNQZ u v) -> x == u && y == v
    (CXor x y z, CXor u v w) -> x == u && y == v && z == w
    (COr x y z, COr u v w) -> x == u && y == v && z == w
    _ -> False

instance Functor Constraint where
  fmap f (CAdd x) = CAdd (fmap f x)
  fmap f (CMul2 x y (Left z)) = CMul2 (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMul2 x y (Right z)) = CMul2 (fmap f x) (fmap f y) (Right (fmap f z))
  fmap _ (CXor x y z) = CXor x y z
  fmap _ (COr x y z) = COr x y z
  fmap _ (CNQZ x y) = CNQZ x y

-- | Smart constructor for the CAdd constraint
cadd :: GaloisField n => n -> [(Var, n)] -> [Constraint n]
cadd !c !xs = map CAdd $ case Poly.buildEither c xs of
  Left _ -> []
  Right xs' -> [xs']

-- | Smart constructor for the CAdd constraint
cmul :: GaloisField n => [(Var, n)] -> [(Var, n)] -> (n, [(Var, n)]) -> [Constraint n]
cmul !xs !ys (c, zs) = case ( do
                                xs' <- Poly.buildEither 0 xs
                                ys' <- Poly.buildEither 0 ys
                                return $ CMul2 xs' ys' (Poly.buildEither c zs)
                            ) of
  Left _ -> []
  Right result -> [result]

instance (GaloisField n, Integral n) => Show (Constraint n) where
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
  show (CXor x y z) = "X $" <> show x <> " ⊕ $" <> show y <> " = $" <> show z
  show (COr x y z) = "O $" <> show x <> " ∨ $" <> show y <> " = $" <> show z

instance GaloisField n => Ord (Constraint n) where
  {-# SPECIALIZE instance Ord (Constraint GF181) #-}

  -- CXor is always greater than anything
  compare (COr x y z) (COr u v w) = compare (x, y, z) (u, v, w)
  compare _ COr {} = LT
  compare COr {} _ = GT
  -- CXor
  compare (CXor x y z) (CXor u v w) = compare (x, y, z) (u, v, w)
  compare _ CXor {} = LT
  compare CXor {} _ = GT
  -- CMul2
  compare (CMul2 aV bV cV) (CMul2 aX bX cX) = compare (aV, bV, cV) (aX, bX, cX)
  compare _ CMul2 {} = LT
  compare CMul2 {} _ = GT
  -- CAdd
  compare (CAdd xs) (CAdd ys) =
    if xs == ys then EQ else compare xs ys
  -- CNQZ
  compare CNQZ {} CNQZ {} = EQ
  compare CNQZ {} _ = LT
  compare _ CNQZ {} = GT

--------------------------------------------------------------------------------

-- | Return the list of variables occurring in constraints
varsInConstraint :: Constraint a -> IntSet
varsInConstraint (CAdd xs) = Poly.vars xs
varsInConstraint (CMul2 aV bV (Left _)) = IntSet.unions $ map Poly.vars [aV, bV]
varsInConstraint (CMul2 aV bV (Right cV)) = IntSet.unions $ map Poly.vars [aV, bV, cV]
varsInConstraint (CNQZ x y) = IntSet.fromList [x, y]
varsInConstraint (CXor x y z) = IntSet.fromList [x, y, z]
varsInConstraint (COr x y z) = IntSet.fromList [x, y, z]

varsInConstraints :: Set (Constraint a) -> IntSet
varsInConstraints = IntSet.unions . Set.map varsInConstraint

--------------------------------------------------------------------------------

-- | Constraint System
data ConstraintSystem n = ConstraintSystem
  { -- | Constraints
    csConstraints :: !(Set (Constraint n)),
    -- | Input variables that are Booleans
    -- should generate constraints like $A * $A = $A for each Boolean variables
    csBooleanInputVars :: !IntSet,
    csVars :: !IntSet,
    -- | Invariant: input variables are placed in the front of everything
    --              so that we only need to remember how many are there
    csInputVarSize :: !Int,
    -- | Invariant: output variables are placed after input variables
    --              so that we only need to remember how many are there
    csOutputVarSize :: !Int
  }
  deriving (Eq, Generic, NFData)

-- | return the number of constraints (including constraints of boolean input vars)
numberOfConstraints :: ConstraintSystem n -> Int
numberOfConstraints (ConstraintSystem cs cs' _ _ _) = Set.size cs + IntSet.size cs'

instance (GaloisField n, Integral n) => Show (ConstraintSystem n) where
  show (ConstraintSystem constraints boolInputVars vars inputVarSize outputVarSize) =
    "ConstraintSystem {\n\
    \  constraints ("
      <> show (length constraints)
      <> "):\n\n"
      <> printConstraints (toList constraints)
      <> "\n"
      <> printBooleanVars
      <> printNumOfVars
      <> printInputVars
      <> printOutputVars
      <> "\n}"
    where
      printConstraints = unlines . map (\c -> "    " <> show c)

      printBooleanVars =
        if IntSet.null boolInputVars
          then ""
          else
            "  boolean input variables (" <> show (IntSet.size boolInputVars)
              <> ")\n\n"

      printNumOfVars =
        "  number of variables: "
          <> show (IntSet.size vars)
          <> "\n"

      printInputVars =
        "  input  variables (" <> show inputVarSize <> "): "
          <> ( case inputVarSize of
                 0 -> "none"
                 1 -> "$0"
                 _ -> "$0 .. $" <> show (inputVarSize - 1)
             )
          <> "\n"

      printOutputVars =
        "  output variables (" <> show outputVarSize <> "): "
          <> ( case outputVarSize of
                 0 -> "none"
                 1 -> "$" <> show inputVarSize
                 _ ->
                   "$" <> show inputVarSize
                     <> " .. $"
                     <> show (inputVarSize + outputVarSize - 1)
             )
          <> "\n"

-- | Sequentially renumber term variables '0..max_var'.  Return
--   renumbered constraints, together with the total number of
--   variables in the (renumbered) constraint set and the (possibly
--   renumbered) in and out variables.
renumberConstraints :: GaloisField n => ConstraintSystem n -> ConstraintSystem n
renumberConstraints cs =
  ConstraintSystem
    (Set.map renumberConstraint (csConstraints cs))
    (IntSet.map renumber (csBooleanInputVars cs))
    (IntSet.fromList renumberedVars)
    (csInputVarSize cs)
    (csOutputVarSize cs)
  where
    -- variables in constraints (that should be kept after renumbering!)
    vars = varsInConstraints (csConstraints cs)
    -- variables in constraints excluding input variables
    otherVars = IntSet.filter (>= csInputVarSize cs) vars
    -- new variables after renumbering (excluding input variables)
    -- we start counting these variables from `csInputVarSize cs`
    -- because we want to keep the input variables intact
    renumberedOtherVars = [csInputVarSize cs .. csInputVarSize cs + IntSet.size otherVars - 1]

    -- all variables after renumbering
    renumberedVars = [0 .. csInputVarSize cs + IntSet.size otherVars - 1]

    -- mapping of old variables to new variables
    -- input variables are placed in the front
    variableMap = Map.fromList $ zip (IntSet.toList otherVars) renumberedOtherVars

    renumber var =
      if var >= csInputVarSize cs
        then case Map.lookup var variableMap of
          Nothing ->
            error
              ( "can't find a mapping for variable " ++ show var
                  ++ " \nmapping: "
                  ++ show variableMap
                  ++ " \nrenumbered vars: "
                  ++ show renumberedVars
              )
          Just var' -> var'
        else var -- this is an input variable
    renumberConstraint constraint = case constraint of
      CAdd xs ->
        CAdd $ Poly.mapVars renumber xs
      CMul2 aV bV cV ->
        CMul2 (Poly.mapVars renumber aV) (Poly.mapVars renumber bV) (Poly.mapVars renumber <$> cV)
      CNQZ x y ->
        CNQZ (renumber x) (renumber y)
      CXor x y z ->
        CXor (renumber x) (renumber y) (renumber z)
      COr x y z ->
        COr (renumber x) (renumber y) (renumber z)

