{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Keelung.Compiler.Relocated where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Map qualified as Map
import Data.Sequence (Seq)
import GHC.Generics (Generic)
import Keelung.Constraint.R1C (R1C (..))
import Keelung.Constraint.R1CS (CNEQ (..))
import Keelung.Data.BinRep (BinRep)
import Keelung.Data.BinRep qualified as BinRep
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Field
import Keelung.Syntax (Var)
import Keelung.Syntax.Counters
import Control.Arrow (left)

--------------------------------------------------------------------------------

-- | Constraint
--      CAdd: 0 = c + c₀x₀ + c₁x₁ ... cₙxₙ
--      CMul: ax * by = c or ax * by = cz
--      CNEq: if (x - y) == 0 then m = 0 else m = recip (x - y)
data Constraint n
  = CAdd !(Poly n)
  | CMul !(Poly n) !(Poly n) !(Either n (Poly n))
  | CNEq (CNEQ n) -- x y m
  deriving (Generic, NFData)

instance GaloisField n => Eq (Constraint n) where
  xs == ys = case (xs, ys) of
    (CAdd x, CAdd y) -> x == y
    (CMul x y z, CMul u v w) ->
      (x == u && y == v || x == v && y == u) && z == w
    (CNEq x, CNEq y) -> x == y
    _ -> False

instance Functor Constraint where
  fmap f (CAdd x) = CAdd (fmap f x)
  fmap f (CMul x y (Left z)) = CMul (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMul x y (Right z)) = CMul (fmap f x) (fmap f y) (Right (fmap f z))
  fmap f (CNEq x) = CNEq (fmap f x)

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
  show (CAdd xs) = "A " <> show xs <> " = 0"
  show (CMul aV bV cV) = "M " <> show (R1C (Right aV) (Right bV) cV)
  show (CNEq x) = show x

instance GaloisField n => Ord (Constraint n) where
  {-# SPECIALIZE instance Ord (Constraint GF181) #-}

  -- CMul
  compare (CMul aV bV cV) (CMul aX bX cX) = compare (aV, bV, cV) (aX, bX, cX)
  compare _ CMul {} = LT
  compare CMul {} _ = GT
  -- CAdd
  compare (CAdd xs) (CAdd ys) = compare xs ys
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

varsInConstraints :: Seq (Constraint a) -> IntSet
varsInConstraints = IntSet.unions . fmap varsInConstraint

--------------------------------------------------------------------------------

-- | Relocated Constraint System
data RelocatedConstraintSystem n = RelocatedConstraintSystem
  { -- | Constraints
    csUseNewOptimizer :: Bool,
    csConstraints :: !(Seq (Constraint n)),
    csBinReps :: [BinRep],
    csCounters :: Counters,
    csDivMods :: [(Either Var n, Either Var n, Either Var n, Either Var n)],
    csModInvs :: [(Var, Var, Integer)]
  }
  deriving (Eq, Generic, NFData)

-- | return the number of constraints (including constraints of boolean input vars)
numberOfConstraints :: RelocatedConstraintSystem n -> Int
numberOfConstraints (RelocatedConstraintSystem _ cs binReps counters _divMods _modInvs) =
  length cs + getBooleanConstraintSize counters + length binReps

instance (GaloisField n, Integral n) => Show (RelocatedConstraintSystem n) where
  show (RelocatedConstraintSystem _ constraints binReps counters _divMods _modInvs) =
    "ConstraintSystem {\n"
      <> prettyConstraints counters (toList constraints) binReps
      <> prettyVariables counters
      <> "\n}"

-- | Sequentially renumber term variables '0..max_var'.  Return
--   renumbered constraints, together with the total number of
--   variables in the (renumbered) constraint set and the (possibly
--   renumbered) in and out variables.
renumberConstraints :: (GaloisField n, Integral n) => RelocatedConstraintSystem n -> RelocatedConstraintSystem n
renumberConstraints cs =
  cs
    { csConstraints = fmap renumberConstraint (csConstraints cs),
      csBinReps = if csUseNewOptimizer cs then fmap renumberBinRep (csBinReps cs) else csBinReps cs,
      csCounters = setReducedCount reducedCount counters,
      csDivMods = fmap renumberDivMod (csDivMods cs),
      csModInvs = fmap renumberModInv (csModInvs cs)
    }
  where
    counters = csCounters cs
    pinnedVarSize = getCountBySort OfPublicInput counters + getCountBySort OfPrivateInput counters + getCountBySort OfOutput counters

    -- variables in constraints (that should be kept after renumbering!)
    varsInBinReps =
      IntSet.fromList $
        concatMap (\binRep -> BinRep.binRepVar binRep : [BinRep.binRepBitStart binRep .. BinRep.binRepBitStart binRep + BinRep.binRepWidth binRep - 1]) (getBinReps counters)
    -- ([var | binRep <- getBinReps counters, var <- [BinRep.binRepBitStart binRep .. BinRep.binRepBitStart binRep + BinRep.binRepWidth binRep - 1]])
    vars = varsInConstraints (csConstraints cs) <> varsInBinReps
    -- variables in constraints excluding input & output variables
    newIntermediateVars = IntSet.filter (>= pinnedVarSize) vars
    -- numbers of variables reduced via renumbering
    reducedCount = getCountBySort OfIntermediate counters - IntSet.size newIntermediateVars
    -- new variables after renumbering (excluding input & output variables)
    renumberedIntermediateVars = [pinnedVarSize .. pinnedVarSize + IntSet.size newIntermediateVars - 1]

    -- all variables after renumbering
    renumberedVars = [0 .. pinnedVarSize + IntSet.size newIntermediateVars - 1]

    -- mapping of old variables to new variables
    -- input variables are placed in the front
    variableMap = Map.fromList $ zip (IntSet.toList newIntermediateVars) renumberedIntermediateVars

    renumber var =
      if var >= pinnedVarSize
        then case Map.lookup var variableMap of
          Nothing ->
            error
              ( "can't find a mapping for variable "
                  <> show var
                  <> " \nmapping: "
                  <> show variableMap
                  <> " \nrenumbered vars: "
                  <> show renumberedVars
              )
          Just var' -> var'
        else var -- this is an input variable
    renumberConstraint constraint = case constraint of
      CAdd xs ->
        CAdd $ Poly.renumberVars renumber xs
      CMul aV bV cV ->
        CMul (Poly.renumberVars renumber aV) (Poly.renumberVars renumber bV) (Poly.renumberVars renumber <$> cV)
      CNEq (CNEQ (Left x) (Left y) m) ->
        CNEq (CNEQ (Left (renumber x)) (Left (renumber y)) (renumber m))
      CNEq (CNEQ (Left x) (Right y) m) ->
        CNEq (CNEQ (Left (renumber x)) (Right y) (renumber m))
      CNEq (CNEQ (Right x) (Left y) m) ->
        CNEq (CNEQ (Right x) (Left (renumber y)) (renumber m))
      CNEq (CNEQ (Right x) (Right y) m) ->
        CNEq (CNEQ (Right x) (Right y) (renumber m))

    renumberBinRep binRep =
      binRep
        { BinRep.binRepVar = renumber (BinRep.binRepVar binRep),
          BinRep.binRepBitStart = renumber (BinRep.binRepBitStart binRep)
        }

    renumberDivMod (x, y, q, r) =
      ( left renumber x,
        left renumber y,
        left renumber q,
        left renumber r
      )

    renumberModInv (x, n, p) = (renumber x, renumber n, p)