{-# LANGUAGE DataKinds #-}

-- | Polynomial of References and Slices
module Test.Data.PolyRS (tests, run) where

import Data.Field.Galois (Prime)
import Data.Map (Map)
import Data.Map qualified as Map
import Keelung (widthOf)
import Keelung.Data.Limb (Limb)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference (Ref)
import Keelung.Data.Slice (Slice)
import Test.Arbitrary ()
import Test.Hspec
import Test.QuickCheck

--------------------------------------------------------------------------------

run :: IO ()
run = hspec tests

toRefMap :: (Integral n) => [(Ref, n)] -> Map Ref n
toRefMap = Map.filter (/= 0) . Map.fromListWith (+)

toLimbMap :: (Integral n) => [(Limb, n)] -> Map Limb n
toLimbMap = Map.filterWithKey (\limb n -> not (Limb.null limb) && n /= 0) . Map.fromListWith (+)

toSliceMap :: (Integral n) => [(Slice, n)] -> Map Slice n
toSliceMap = Map.filterWithKey (\slice n -> widthOf slice /= 0 && n /= 0) . Map.fromListWith (+)

mergeRefMap :: (Integral n) => Map Ref n -> Map Ref n -> Map Ref n
mergeRefMap xs ys = Map.filter (/= 0) (Map.unionWith (+) xs ys)

mergeLimbMap :: (Integral n) => Map Limb n -> Map Limb n -> Map Limb n
mergeLimbMap xs ys = Map.filterWithKey (\limb n -> not (Limb.null limb) && n /= 0) (Map.unionWith (+) xs ys)

-- NOTE: this implementation is incorrect
-- mergeSliceMap :: (Integral n) => Map Slice n -> Map Slice n -> Map Slice n
-- mergeSliceMap xs ys = Map.filterWithKey (\slice n -> widthOf slice /= 0 && n /= 0) (Map.unionWith (+) xs ys)

tests :: SpecWith ()
tests = describe "PolyRS" $ do
  it "should be valid" $ do
    property $ \poly -> do
      PolyL.validate (poly :: PolyL (Prime 17)) `shouldBe` Nothing

  describe "fromLimbs" $ do
    it "should result in valid PolyL" $ do
      property $ \(constant, limbs) -> do
        case PolyL.fromLimbs constant limbs of
          Left constant' -> do
            constant' `shouldBe` constant
            null (toLimbMap limbs) `shouldBe` True
          Right poly -> do
            PolyL.polyConstant poly `shouldBe` constant
            PolyL.polyLimbs poly `shouldBe` toLimbMap limbs
            PolyL.validate (poly :: PolyL (Prime 17)) `shouldBe` Nothing

  describe "fromRefs" $ do
    it "should result in valid PolyL" $ do
      property $ \(constant, refs) -> do
        case PolyL.fromRefs constant refs of
          Left constant' -> do
            constant' `shouldBe` constant
            null (toRefMap refs) `shouldBe` True
          Right poly -> do
            PolyL.polyConstant poly `shouldBe` constant
            PolyL.polyRefs poly `shouldBe` toRefMap refs
            PolyL.validate (poly :: PolyL (Prime 17)) `shouldBe` Nothing

  describe "insertSlices" $ do
    it "should result in valid PolyL" $ do
      property $ \(slices, poly) -> do
        case PolyL.insertSlices slices poly of
          Left constant' -> do
            constant' `shouldBe` PolyL.polyConstant poly
            null (toSliceMap slices) && null (PolyL.polyRefs poly) `shouldBe` True
          Right polynomial -> do
            PolyL.polyConstant (polynomial :: PolyL (Prime 17)) `shouldBe` PolyL.polyConstant poly
            PolyL.polyRefs polynomial `shouldBe` PolyL.polyRefs poly
            -- dunno how to check this
            -- toSliceMap (PolyL.toSlices polynomial) `shouldBe` toSliceMap (PolyL.toSlices poly) `mergeSliceMap` toSliceMap slices
            PolyL.validate polynomial `shouldBe` Nothing

  describe "insertRefs" $ do
    it "should result in valid PolyL" $ do
      property $ \(constant, refs, poly) -> do
        case PolyL.insertRefs constant refs poly of
          Left constant' -> do
            constant' `shouldBe` constant + PolyL.polyConstant poly
            null (toRefMap refs) && null (PolyL.polyLimbs poly) `shouldBe` True
          Right polynomial -> do
            PolyL.polyConstant (polynomial :: PolyL (Prime 17)) `shouldBe` constant + PolyL.polyConstant poly
            PolyL.polyLimbs polynomial `shouldBe` PolyL.polyLimbs poly
            PolyL.polyRefs polynomial `shouldBe` PolyL.polyRefs poly `mergeRefMap` toRefMap refs
            PolyL.validate polynomial `shouldBe` Nothing

  describe "addConstant" $ do
    it "should result in valid PolyL" $ do
      property $ \(constant, poly) -> do
        let polynomial = PolyL.addConstant constant poly :: PolyL (Prime 17)
        PolyL.polyConstant polynomial `shouldBe` constant + PolyL.polyConstant poly
        PolyL.polyLimbs polynomial `shouldBe` PolyL.polyLimbs poly
        PolyL.polyRefs polynomial `shouldBe` PolyL.polyRefs poly
        PolyL.validate polynomial `shouldBe` Nothing

  describe "multiplyBy" $ do
    it "should result in valid PolyL" $ do
      property $ \(m, poly) -> do
        case PolyL.multiplyBy m (poly :: PolyL (Prime 17)) of
          Left constant' -> do
            constant' `shouldBe` 0
          Right polynomial -> do
            PolyL.polyConstant polynomial `shouldBe` PolyL.polyConstant poly * m
            PolyL.polyLimbs polynomial `shouldBe` fmap (m *) (PolyL.polyLimbs poly)
            PolyL.polyRefs polynomial `shouldBe` fmap (m *) (PolyL.polyRefs poly)
            PolyL.validate polynomial `shouldBe` Nothing

  describe "merge" $ do
    it "should result in valid PolyL" $ do
      property $ \(poly1, poly2) -> do
        case PolyL.merge poly1 (poly2 :: PolyL (Prime 17)) of
          Left constant' -> do
            constant' `shouldBe` PolyL.polyConstant poly1 + PolyL.polyConstant poly2
          Right polynomial -> do
            PolyL.polyConstant polynomial `shouldBe` PolyL.polyConstant poly1 + PolyL.polyConstant poly2
            PolyL.polyLimbs polynomial `shouldBe` PolyL.polyLimbs poly1 `mergeLimbMap` PolyL.polyLimbs poly2
            PolyL.polyRefs polynomial `shouldBe` PolyL.polyRefs poly1 `mergeRefMap` PolyL.polyRefs poly2
            PolyL.validate polynomial `shouldBe` Nothing

  describe "negate" $ do
    it "should result in valid PolyL" $ do
      property $ \poly -> do
        let polynomial = PolyL.negate (poly :: PolyL (Prime 17))
        PolyL.polyConstant polynomial `shouldBe` -PolyL.polyConstant poly
        PolyL.polyLimbs polynomial `shouldBe` fmap negate (PolyL.polyLimbs poly)
        PolyL.polyRefs polynomial `shouldBe` fmap negate (PolyL.polyRefs poly)
        PolyL.validate polynomial `shouldBe` Nothing