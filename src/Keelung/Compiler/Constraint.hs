{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Keelung.Compiler.Constraint where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Keelung.Constraint.Polynomial (Poly)
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Constraint.R1C (R1C (..))
import Keelung.Constraint.R1CS (CNEQ (..))
import Keelung.Field
import Keelung.Types (Var)

--------------------------------------------------------------------------------

-- | Constraint
--      CAdd: 0 = c + c₀x₀ + c₁x₁ ... cₙxₙ
--      CMul: ax * by = c or ax * by = cz
--      CNEq: if (x - y) == 0 then m = 0 else m = recip (x - y)
--      CXor: x ⊕ y = z
--      COr: x ∨ y = z
data Constraint n
  = CAdd !(Poly n)
  | CMul !(Poly n) !(Poly n) !(Either n (Poly n))
  | CNEq (CNEQ n) -- x y m
  | CXor Var Var Var
  | COr Var Var Var
  deriving (Generic, NFData)

instance GaloisField n => Eq (Constraint n) where
  xs == ys = case (xs, ys) of
    (CAdd x, CAdd y) -> x == y
    (CMul x y z, CMul u v w) ->
      (x == u && y == v || x == v && y == u) && z == w
    (CNEq x, CNEq y) -> x == y
    (CXor x y z, CXor u v w) -> x == u && y == v && z == w
    (COr x y z, COr u v w) -> x == u && y == v && z == w
    _ -> False

instance Functor Constraint where
  fmap f (CAdd x) = CAdd (fmap f x)
  fmap f (CMul x y (Left z)) = CMul (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMul x y (Right z)) = CMul (fmap f x) (fmap f y) (Right (fmap f z))
  fmap f (CNEq x) = CNEq (fmap f x)
  fmap _ (CXor x y z) = CXor x y z
  fmap _ (COr x y z) = COr x y z

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
                                return $ CMul xs' ys' (Poly.buildEither c zs)
                            ) of
  Left _ -> []
  Right result -> [result]

instance (GaloisField n, Integral n) => Show (Constraint n) where
  show (CAdd xs) = "A " ++ show xs ++ " = 0"
  show (CMul aV bV cV) = "M " <> show (R1C (Right aV) (Right bV) cV)
  show (CNEq x) = show x
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
  -- CMul
  compare (CMul aV bV cV) (CMul aX bX cX) = compare (aV, bV, cV) (aX, bX, cX)
  compare _ CMul {} = LT
  compare CMul {} _ = GT
  -- CAdd
  compare (CAdd xs) (CAdd ys) =
    if xs == ys then EQ else compare xs ys
  -- CNEq
  compare CNEq {} CNEq {} = EQ
  compare CNEq {} _ = LT
  compare _ CNEq {} = GT

--------------------------------------------------------------------------------

-- | Return the list of variables occurring in constraints
varsInConstraint :: Constraint a -> IntSet
varsInConstraint (CAdd xs) = Poly.vars xs
varsInConstraint (CMul aV bV (Left _)) = IntSet.unions $ map Poly.vars [aV, bV]
varsInConstraint (CMul aV bV (Right cV)) = IntSet.unions $ map Poly.vars [aV, bV, cV]
varsInConstraint (CNEq (CNEQ (Left x) (Left y) m)) = IntSet.fromList [x, y, m]
varsInConstraint (CNEq (CNEQ (Left x) _ m)) = IntSet.fromList [x, m]
varsInConstraint (CNEq (CNEQ _ (Left y) m)) = IntSet.fromList [y, m]
varsInConstraint (CNEq (CNEQ _ _ m)) = IntSet.fromList [m]
varsInConstraint (CXor x y z) = IntSet.fromList [x, y, z]
varsInConstraint (COr x y z) = IntSet.fromList [x, y, z]

varsInConstraints :: Set (Constraint a) -> IntSet
varsInConstraints = IntSet.unions . Set.map varsInConstraint

--------------------------------------------------------------------------------

-- | Constraint System
data ConstraintSystem n = ConstraintSystem
  { -- | Constraints
    csConstraints :: !(Set (Constraint n)),
    -- | Variables that are Booleans
    -- should generate constraints like $A * $A = $A for each Boolean variables
    csBoolVars :: !IntSet,
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
  show (ConstraintSystem constraints boolVars vars inputVarSize outputVarSize) =
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
        if IntSet.null boolVars
          then ""
          else
            "  boolean variables (" <> show (IntSet.size boolVars)
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
    (IntSet.map renumber (csBoolVars cs))
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
      CMul aV bV cV ->
        CMul (Poly.mapVars renumber aV) (Poly.mapVars renumber bV) (Poly.mapVars renumber <$> cV)
      CNEq (CNEQ (Left x) (Left y) m) ->
        CNEq (CNEQ (Left (renumber x)) (Left (renumber y)) (renumber m))
      CNEq (CNEQ (Left x) (Right y) m) ->
        CNEq (CNEQ (Left (renumber x)) (Right y) (renumber m))
      CNEq (CNEQ (Right x) (Left y) m) ->
        CNEq (CNEQ (Right x) (Left (renumber y)) (renumber m))
      CNEq (CNEQ (Right x) (Right y) m) ->
        CNEq (CNEQ (Right x) (Right y) (renumber m))
      CXor x y z ->
        CXor (renumber x) (renumber y) (renumber z)
      COr x y z ->
        COr (renumber x) (renumber y) (renumber z)
