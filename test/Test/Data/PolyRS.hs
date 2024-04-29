{-# LANGUAGE DataKinds #-}

-- | Polynomial of References and Slices
module Test.Data.PolyRS (tests, run) where

import Data.Bifunctor (second)
import Data.Field.Galois (Prime)
import Data.Map (Map)
import Data.Map qualified as Map
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.SlicePolynomial qualified as SlicePoly
import Test.Arbitrary ()
import Test.Hspec
import Test.QuickCheck

--------------------------------------------------------------------------------

run :: IO ()
run = hspec tests

toRefMap :: (Integral n) => [(Ref, n)] -> Map Ref n
toRefMap = Map.filter (/= 0) . Map.fromListWith (+)

mergeRefMap :: (Integral n) => Map Ref n -> Map Ref n -> Map Ref n
mergeRefMap xs ys = Map.filter (/= 0) (Map.unionWith (+) xs ys)

tests :: SpecWith ()
tests = describe "PolyRS" $ do
  it "should be valid" $ do
    property $ \poly -> do
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

  describe "addConstant" $ do
    it "should result in valid PolyL" $ do
      property $ \(constant, poly) -> do
        let polynomial = PolyL.addConstant constant poly :: PolyL (Prime 17)
        PolyL.polyConstant polynomial `shouldBe` constant + PolyL.polyConstant poly
        PolyL.toSlices polynomial `shouldBe` PolyL.toSlices poly
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
            PolyL.toSlices polynomial `shouldBe` fmap (second (m *)) (PolyL.toSlices poly)
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
            SlicePoly.fromSlices (PolyL.toSlices polynomial) `shouldBe` SlicePoly.fromSlices (PolyL.toSlices poly1) <> SlicePoly.fromSlices (PolyL.toSlices poly2)
            PolyL.polyRefs polynomial `shouldBe` PolyL.polyRefs poly1 `mergeRefMap` PolyL.polyRefs poly2
            PolyL.validate polynomial `shouldBe` Nothing
  describe "negate" $ do
    it "should result in valid PolyL" $ do
      property $ \poly -> do
        let polynomial = PolyL.negate (poly :: PolyL (Prime 17))
        PolyL.polyConstant polynomial `shouldBe` -PolyL.polyConstant poly
        PolyL.toSlices polynomial `shouldBe` fmap (second ((-1) *)) (PolyL.toSlices poly)
        PolyL.polyRefs polynomial `shouldBe` fmap negate (PolyL.polyRefs poly)
        PolyL.validate polynomial `shouldBe` Nothing