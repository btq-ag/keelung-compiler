{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.ConstraintSystem where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.Sequence (Seq)
import GHC.Generics (Generic)
import Keelung.Constraint.R1C (R1C (..))
import Keelung.Data.FieldInfo
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Field
import Keelung.Syntax (Var, Width)
import Keelung.Syntax.Counters hiding (prettyConstraints)

--------------------------------------------------------------------------------

-- | Constraint
--      CAdd: 0 = c + c₀x₀ + c₁x₁ ... cₙxₙ
--      CMul: ax * by = c or ax * by = cz
data Constraint n
  = CAdd !(Poly n)
  | CMul !(Poly n) !(Poly n) !(Either n (Poly n))
  deriving (Generic, NFData)

instance GaloisField n => Eq (Constraint n) where
  xs == ys = case (xs, ys) of
    (CAdd x, CAdd y) -> x == y
    (CMul x y z, CMul u v w) ->
      (x == u && y == v || x == v && y == u) && z == w
    _ -> False

instance Functor Constraint where
  fmap f (CAdd x) = CAdd (fmap f x)
  fmap f (CMul x y (Left z)) = CMul (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMul x y (Right z)) = CMul (fmap f x) (fmap f y) (Right (fmap f z))

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
  show (CAdd xs) = show xs <> " = 0"
  show (CMul aV bV cV) = show (R1C (Right aV) (Right bV) cV)

instance GaloisField n => Ord (Constraint n) where
  {-# SPECIALIZE instance Ord (Constraint GF181) #-}

  -- CMul
  compare (CMul aV bV cV) (CMul aX bX cX) = compare (aV, bV, cV) (aX, bX, cX)
  compare _ CMul {} = LT
  compare CMul {} _ = GT
  -- CAdd
  compare (CAdd xs) (CAdd ys) = compare xs ys

--------------------------------------------------------------------------------

-- | Return the list of variables occurring in constraints
-- varsInConstraint :: Constraint a -> IntSet
-- varsInConstraint (CAdd xs) = Poly.vars xs
-- varsInConstraint (CMul aV bV (Left _)) = IntSet.unions $ map Poly.vars [aV, bV]
-- varsInConstraint (CMul aV bV (Right cV)) = IntSet.unions $ map Poly.vars [aV, bV, cV]

-- varsInConstraints :: Seq (Constraint a) -> IntSet
-- varsInConstraints = IntSet.unions . fmap varsInConstraint

--------------------------------------------------------------------------------

-- | Linked Constraint System
data ConstraintSystem n = ConstraintSystem
  { -- | Constraints
    csField :: FieldInfo,
    csConstraints :: !(Seq (Constraint n)),
    csCounters :: Counters,
    csEqZeros :: [(Poly n, Var)],
    csDivMods :: [((Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer))],
    csModInvs :: [((Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer), Integer)]
  }
  deriving (Eq, Generic, NFData, Functor)

-- | return the number of constraints (including constraints of boolean input vars)
numberOfConstraints :: ConstraintSystem n -> Int
numberOfConstraints (ConstraintSystem _ cs counters _eqs _divMods _modInvs) =
  length cs + getBooleanConstraintCount counters

instance (GaloisField n, Integral n) => Show (ConstraintSystem n) where
  show (ConstraintSystem _ constraints counters _eqs _divMods _modInvs) =
    "ConstraintSystem {\n"
      <> prettyConstraints counters (toList constraints)
      <> prettyVariables counters
      <> "\n}"

prettyConstraints :: Show constraint => Counters -> [constraint] -> String
prettyConstraints counters cs =
  showConstraintSummary
    <> showOrdinaryConstraints
    <> showBooleanConstraints
  where
    -- sizes of constraint groups
    booleanConstraintSize = getBooleanConstraintCount counters
    ordinaryConstraintSize = length cs

    -- summary of constraint groups
    showConstraintSummary =
      "  Constriant ("
        <> show (ordinaryConstraintSize + booleanConstraintSize)
        <> "): \n"

    -- Ordinary constraints
    showOrdinaryConstraints =
      if ordinaryConstraintSize == 0
        then ""
        else
          "    Ordinary constraints ("
            <> show ordinaryConstraintSize
            <> "):\n\n"
            <> unlines (map (\x -> "      " <> show x) cs)
            <> "\n"

    -- Boolean constraints
    showBooleanConstraints =
      if booleanConstraintSize == 0
        then ""
        else
          "    Boolean constraints ("
            <> show booleanConstraintSize
            <> "):\n\n"
            <> unlines (map ("      " <>) (prettyBooleanConstraints counters))
            <> "\n"