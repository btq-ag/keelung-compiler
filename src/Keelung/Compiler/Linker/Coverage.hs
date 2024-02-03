{-# LANGUAGE FlexibleInstances #-}

-- | Module for generating coverage information for the linker for testing purposes
module Keelung.Compiler.Linker.Coverage (isValid) where

import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.Map qualified as Map
import Data.Sequence (Seq)
import Data.Set (Set)
import Data.Set qualified as Set
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.Linker
import Keelung.Data.Constraint (Constraint (..))
import Keelung.Data.Limb (Limb)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)

isValid :: (Integral n, GaloisField n) => ConstraintModule n -> Bool
isValid cm = coverageIsValid $ generateCoverage (constructEnv cm) cm

--------------------------------------------------------------------------------

-- | Datatype for keeping track of which Ref is mapped to which Var
newtype Coverage = Coverage (IntMap (Set Ref))

-- | A Coverage is valid if:
--      1. no Var is skipped, i.e. there are no gaps in the IntMap
--      3. no Var is mapped to multiple Refs
coverageIsValid :: Coverage -> Bool
coverageIsValid (Coverage xs) =
  let noSkipped = case IntMap.maxViewWithKey xs of
        Nothing -> True -- empty IntMap
        Just ((k, _), _) -> k == IntMap.size xs - 1
      noMultipleRefs = all (\s -> Set.size s == 1) xs
   in noSkipped && noMultipleRefs

-- | How to combine two coverages
instance Semigroup Coverage where
  Coverage a <> Coverage b = Coverage (IntMap.unionWith (<>) a b)

-- | The empty coverage
instance Monoid Coverage where
  mempty = Coverage IntMap.empty

-- | Typeclass for generating Coverage reports
class GenerateCoverage a where
  generateCoverage :: Env -> a -> Coverage

instance GenerateCoverage Limb where
  generateCoverage env limb =
    Coverage $
      -- precondition of `fromDistinctAscList` is that the keys are in ascending order
      IntMap.fromDistinctAscList
        [ ( reindexRefU
              env
              (Limb.lmbRef limb)
              (i + Limb.lmbOffset limb),
            Set.singleton (B (RefUBit (Limb.lmbRef limb) i))
          )
          | i <- [0 .. Limb.lmbWidth limb - 1]
        ]

instance GenerateCoverage Slice where
  generateCoverage env slice =
    Coverage $
      -- precondition of `fromDistinctAscList` is that the keys are in ascending order
      IntMap.fromDistinctAscList
        [ ( reindexRefU
              env
              (Slice.sliceRefU slice)
              i,
            Set.singleton (B (RefUBit (Slice.sliceRefU slice) i))
          )
          | i <- [Slice.sliceStart slice .. Slice.sliceEnd slice - 1]
        ]

instance (GenerateCoverage a) => GenerateCoverage (Seq a) where
  generateCoverage env xs = mconcat $ map (generateCoverage env) (toList xs)

instance (GenerateCoverage a) => GenerateCoverage [a] where
  generateCoverage env xs = mconcat $ map (generateCoverage env) xs

instance GenerateCoverage RefF where
  generateCoverage env ref = Coverage $ IntMap.singleton (reindexRefF env ref) (Set.singleton (F ref))

instance GenerateCoverage RefB where
  generateCoverage env ref = Coverage $ IntMap.singleton (reindexRefB env ref) (Set.singleton (B ref))

instance GenerateCoverage Ref where
  generateCoverage env (F refF) = generateCoverage env refF
  generateCoverage env (B refB) = generateCoverage env refB

instance GenerateCoverage RefU where
  generateCoverage env refU = generateCoverage env (Limb.refUToLimbs (envFieldWidth env) refU)

instance GenerateCoverage (PolyL n) where
  generateCoverage env poly =
    let limbCoverage = generateCoverage env (fmap fst (PolyL.polyLimbs poly))
        refCoverage = generateCoverage env (Map.keys (PolyL.polyRefs poly))
     in limbCoverage <> refCoverage

instance GenerateCoverage (Constraint n) where
  generateCoverage env (CAddL poly) = generateCoverage env poly
  generateCoverage env (CRefEq x y) = generateCoverage env x <> generateCoverage env y
  generateCoverage env (CRefBNEq x y) = generateCoverage env x <> generateCoverage env y
  generateCoverage env (CLimbEq x y) = generateCoverage env x <> generateCoverage env y
  generateCoverage env (CRefUEq x y) = generateCoverage env x <> generateCoverage env y
  generateCoverage env (CSliceEq x y) = generateCoverage env x <> generateCoverage env y
  generateCoverage env (CRefFVal x _) = generateCoverage env x
  generateCoverage env (CLimbVal x _) = generateCoverage env x
  generateCoverage env (CRefUVal x _) = generateCoverage env x
  generateCoverage env (CMulL a b (Left _)) = generateCoverage env a <> generateCoverage env b
  generateCoverage env (CMulL a b (Right c)) = generateCoverage env a <> generateCoverage env b <> generateCoverage env c
  generateCoverage env (CSliceVal x _) = generateCoverage env x

instance GenerateCoverage (Either RefU U) where
  generateCoverage env (Left refU) = generateCoverage env refU
  generateCoverage _ (Right _) = mempty

instance (Integral n, GaloisField n) => GenerateCoverage (ConstraintModule n) where
  generateCoverage env cm =
    let fromModInvs (a, b, c, _) = generateCoverage env a <> generateCoverage env b <> generateCoverage env c
        fromCLDivMods (a, b, c, d) = generateCoverage env a <> generateCoverage env b <> generateCoverage env c <> generateCoverage env d
        fromDivMods (a, b, c, d) = generateCoverage env a <> generateCoverage env b <> generateCoverage env c <> generateCoverage env d
        fromEqZeros (a, b) = generateCoverage env a <> generateCoverage env b
     in mconcat $
          toList $
            fmap (generateCoverage env) (toConstraints cm env)
              <> fmap fromEqZeros (cmEqZeros cm)
              <> fmap fromDivMods (cmDivMods cm)
              <> fmap fromCLDivMods (cmCLDivMods cm)
              <> fmap fromModInvs (cmModInvs cm)