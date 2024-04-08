{-# LANGUAGE DataKinds #-}

-- | Polynomial of References and Slices
module Test.Data.PolyRS (tests, run) where

import Data.Bifunctor (second)
import Data.Field.Galois (Prime)
import Data.Map (Map)
import Data.Map qualified as Map
import Keelung (widthOf)
import Keelung.Data.Limb (Limb)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice)
import Keelung.Data.SlicePolynomial qualified as SlicePoly
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
            -- PolyL.polyLimbs poly `shouldBe` toLimbMap limbs
            -- SlicePoly.fromSlices (PolyL.toSlices poly) `shouldBe` SlicePoly.fromSlices (PolyL.toSlices poly1)
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
            null (toRefMap refs) && null (PolyL.toSlices poly) `shouldBe` True
          Right polynomial -> do
            PolyL.polyConstant (polynomial :: PolyL (Prime 17)) `shouldBe` constant + PolyL.polyConstant poly
            PolyL.toSlices polynomial `shouldBe` PolyL.toSlices poly
            PolyL.polyRefs polynomial `shouldBe` PolyL.polyRefs poly `mergeRefMap` toRefMap refs
            PolyL.validate polynomial `shouldBe` Nothing

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
  -- TODO: examine this error
  --  test/Test/Data/PolyRS.hs:126:62:
  --   1) PolyRS.merge should result in valid PolyL
  --        Falsifiable (after 33 tests):
  --          (P (1 `modulo` 17) + P (15 `modulo` 17)FO5 + P (2 `modulo` 17)FO6 + P (14 `modulo` 17)FI5 - FP6 + P (13 `modulo` 17)BO5 + P (4 `modulo` 17)BO6 + P (6 `modulo` 17)BO10 + P (11 `modulo` 17)U₁₅5 [13 ... 15) - U₁₇7 [11 ... 12) + P (2 `modulo` 17)U₂₁10 [13 ... 14) + P (8 `modulo` 17)U₂₆1 [14 ... 22) + P (10 `modulo` 17)U₃₁2 [15 ... 22) - UO₂₃4 [13 ... 15) + P (3 `modulo` 17)UO₂₄4 [15 ... 20) + P (2 `modulo` 17)UO₂₅8 [13 ... 17) - UO₂₅4 [13 ... 14) + P (10 `modulo` 17)UO₂₅2 [10 ... 12) + P (8 `modulo` 17)UO₂₆9 [8 ... 11) + P (12 `modulo` 17)UI₁₀4 [5 ... 10) + P (12 `modulo` 17)UI₁₅2 [3 ... 8) + P (15 `modulo` 17)UI₁₆4 [15 ... 16) + P (14 `modulo` 17)UP₁₇4 [11 ... 12) - UP₁₇1 [7 ... 12) + P (2 `modulo` 17)UP₁₇0 [4 ... 7) + P (5 `modulo` 17)UI₁₉6 [4 ... 9) + P (9 `modulo` 17)UP₁₉1 [7 ... 8) + P (15 `modulo` 17)UP₂₅10 [9 ... 14) + P (13 `modulo` 17)UI₂₅0 [6 ... 12) + P (13 `modulo` 17)UI₂₇5 [12 ... 19) + P (10 `modulo` 17)UP₃₂9 [13 ... 21) + P (7 `modulo` 17)UI₃₇9 [16 ... 21),P (16 `modulo` 17) + P (14 `modulo` 17)FO6 + P (3 `modulo` 17)FO7 + P (10 `modulo` 17)FI7 + P (6 `modulo` 17)FI8 + FP2 + P (12 `modulo` 17)FP4 - FP10 + P (7 `modulo` 17)F3 + P (7 `modulo` 17)F8 + P (14 `modulo` 17)F9 + P (15 `modulo` 17)F10 + P (12 `modulo` 17)BO1 + P (11 `modulo` 17)BO8 + P (15 `modulo` 17)BO10 + P (4 `modulo` 17)BI0 + P (13 `modulo` 17)BP3 + P (5 `modulo` 17)B4 + P (5 `modulo` 17)U₁₁9 [6 ... 7) + P (4 `modulo` 17)U₁₄4 [12 ... 14) + P (11 `modulo` 17)U₁₈5 [12 ... 15) + P (2 `modulo` 17)U₂₁10 [1 ... 8) + P (4 `modulo` 17)U₂₁2 [8 ... 16) + P (14 `modulo` 17)U₂₅2 [15 ... 18) - U₂₇9 [9 ... 12) + P (7 `modulo` 17)U₂₈8 [14 ... 16) + P (2 `modulo` 17)U₂₉10 [12 ... 20) + U₂₉4 [7 ... 14) + UO₁₈1 [8 ... 15) + P (14 `modulo` 17)UO₁₉1 [5 ... 9) + P (12 `modulo` 17)UO₂₀7 [7 ... 12) + P (3 `modulo` 17)UO₂₂3 [15 ... 22) + UO₂₂1 [6 ... 11) + P (3 `modulo` 17)UO₂₃9 [11 ... 18) + P (6 `modulo` 17)UO₂₅2 [8 ... 9) + UO₂₆10 [9 ... 10) + P (9 `modulo` 17)UO₂₆9 [8 ... 11) + P (4 `modulo` 17)UO₂₆8 [12 ... 18) + P (15 `modulo` 17)UI₁₆7 [11 ... 12) + UI₁₈6 [4 ... 5) + P (9 `modulo` 17)UI₂₁4 [8 ... 12) - UP₂₅5 [4 ... 10) + P (6 `modulo` 17)UP₃₁1 [14 ... 20) + P (9 `modulo` 17)UP₃₄7 [15 ... 18))
  --        expected: SlicePoly {unSlicePoly = fromList [(U₁₁9,[P (5 `modulo` 17)$6]),(U₁₄4,[P (4 `modulo` 17)($12 ~ $13)]),(U₁₅5,[P (11 `modulo` 17)($13 ~ $14)]),(U₁₇7,[P (16 `modulo` 17)$11]),(U₁₈5,[P (11 `modulo` 17)($12 ~ $14)]),(U₂₁10,[P (2 `modulo` 17)($1 ~ $7), P (15 `modulo` 17)$13]),(U₂₁2,[P (4 `modulo` 17)($8 ~ $15)]),(U₂₅2,[P (14 `modulo` 17)($15 ~ $17)]),(U₂₆1,[P (8 `modulo` 17)($14 ~ $21)]),(U₂₇9,[P (16 `modulo` 17)($9 ~ $11)]),(U₂₈8,[P (7 `modulo` 17)($14 ~ $15)]),(U₂₉10,[P (2 `modulo` 17)($12 ~ $19)]),(U₂₉4,[$7 ~ $13]),(U₃₁2,[P (10 `modulo` 17)($15 ~ $21)]),(UO₁₈1,[$8 ~ $14]),(UO₁₉1,[P (14 `modulo` 17)($5 ~ $8)]),(UO₂₀7,[P (12 `modulo` 17)($7 ~ $11)]),(UO₂₂3,[P (3 `modulo` 17)($15 ~ $21)]),(UO₂₂1,[$6 ~ $10]),(UO₂₃9,[P (3 `modulo` 17)($11 ~ $17)]),(UO₂₃4,[P (16 `modulo` 17)($13 ~ $14)]),(UO₂₄4,[P (3 `modulo` 17)($15 ~ $19)]),(UO₂₅8,[P (2 `modulo` 17)($13 ~ $16)]),(UO₂₅4,[P (16 `modulo` 17)$13]),(UO₂₅2,[P (6 `modulo` 17)$8, P (11 `modulo` 17)($10 ~ $11)]),(UO₂₆10,[$9]),(UO₂₆9,[]),(UO₂₆8,[P (4 `modulo` 17)($12 ~ $17)]),(UI₁₀4,[P (12 `modulo` 17)($5 ~ $9)]),(UI₁₅2,[P (12 `modulo` 17)($3 ~ $7)]),(UI₁₆7,[P (15 `modulo` 17)$11]),(UI₁₆4,[P (15 `modulo` 17)$15]),(UP₁₇4,[P (14 `modulo` 17)$11]),(UP₁₇1,[P (16 `modulo` 17)($7 ~ $11)]),(UP₁₇0,[P (2 `modulo` 17)($4 ~ $6)]),(UI₁₈6,[$4]),(UI₁₉6,[P (5 `modulo` 17)($4 ~ $8)]),(UP₁₉1,[P (9 `modulo` 17)$7]),(UI₂₁4,[P (9 `modulo` 17)($8 ~ $11)]),(UP₂₅10,[P (15 `modulo` 17)($9 ~ $13)]),(UP₂₅5,[P (16 `modulo` 17)($4 ~ $9)]),(UI₂₅0,[P (13 `modulo` 17)($6 ~ $11)]),(UI₂₇5,[P (13 `modulo` 17)($12 ~ $18)]),(UP₃₁1,[P (6 `modulo` 17)($14 ~ $19)]),(UP₃₂9,[P (10 `modulo` 17)($13 ~ $20)]),(UP₃₄7,[P (9 `modulo` 17)($15 ~ $17)]),(UI₃₇9,[P (7 `modulo` 17)($16 ~ $20)])]}
  --         but got: SlicePoly {unSlicePoly = fromList [(U₁₁9,[P (5 `modulo` 17)$6]),(U₁₄4,[P (4 `modulo` 17)($12 ~ $13)]),(U₁₅5,[P (11 `modulo` 17)($13 ~ $14)]),(U₁₇7,[P (16 `modulo` 17)$11]),(U₁₈5,[P (11 `modulo` 17)($12 ~ $14)]),(U₂₁10,[P (2 `modulo` 17)($1 ~ $7), P (15 `modulo` 17)$13]),(U₂₁2,[P (4 `modulo` 17)($8 ~ $15)]),(U₂₅2,[P (14 `modulo` 17)($15 ~ $17)]),(U₂₆1,[P (8 `modulo` 17)($14 ~ $21)]),(U₂₇9,[P (16 `modulo` 17)($9 ~ $11)]),(U₂₈8,[P (7 `modulo` 17)($14 ~ $15)]),(U₂₉10,[P (2 `modulo` 17)($12 ~ $19)]),(U₂₉4,[$7 ~ $13]),(U₃₁2,[P (10 `modulo` 17)($15 ~ $21)]),(UO₁₈1,[$8 ~ $14]),(UO₁₉1,[P (14 `modulo` 17)($5 ~ $8)]),(UO₂₀7,[P (12 `modulo` 17)($7 ~ $11)]),(UO₂₂3,[P (3 `modulo` 17)($15 ~ $21)]),(UO₂₂1,[$6 ~ $10]),(UO₂₃9,[P (3 `modulo` 17)($11 ~ $17)]),(UO₂₃4,[P (16 `modulo` 17)($13 ~ $14)]),(UO₂₄4,[P (3 `modulo` 17)($15 ~ $19)]),(UO₂₅8,[P (2 `modulo` 17)($13 ~ $16)]),(UO₂₅4,[P (16 `modulo` 17)$13]),(UO₂₅2,[P (6 `modulo` 17)$8, P (11 `modulo` 17)($10 ~ $11)]),(UO₂₆10,[$9]),(UO₂₆8,[P (4 `modulo` 17)($12 ~ $17)]),(UI₁₀4,[P (12 `modulo` 17)($5 ~ $9)]),(UI₁₅2,[P (12 `modulo` 17)($3 ~ $7)]),(UI₁₆7,[P (15 `modulo` 17)$11]),(UI₁₆4,[P (15 `modulo` 17)$15]),(UP₁₇4,[P (14 `modulo` 17)$11]),(UP₁₇1,[P (16 `modulo` 17)($7 ~ $11)]),(UP₁₇0,[P (2 `modulo` 17)($4 ~ $6)]),(UI₁₈6,[$4]),(UI₁₉6,[P (5 `modulo` 17)($4 ~ $8)]),(UP₁₉1,[P (9 `modulo` 17)$7]),(UI₂₁4,[P (9 `modulo` 17)($8 ~ $11)]),(UP₂₅10,[P (15 `modulo` 17)($9 ~ $13)]),(UP₂₅5,[P (16 `modulo` 17)($4 ~ $9)]),(UI₂₅0,[P (13 `modulo` 17)($6 ~ $11)]),(UI₂₇5,[P (13 `modulo` 17)($12 ~ $18)]),(UP₃₁1,[P (6 `modulo` 17)($14 ~ $19)]),(UP₃₂9,[P (10 `modulo` 17)($13 ~ $20)]),(UP₃₄7,[P (9 `modulo` 17)($15 ~ $17)]),(UI₃₇9,[P (7 `modulo` 17)($16 ~ $20)])]}
  describe "negate" $ do
    it "should result in valid PolyL" $ do
      property $ \poly -> do
        let polynomial = PolyL.negate (poly :: PolyL (Prime 17))
        PolyL.polyConstant polynomial `shouldBe` -PolyL.polyConstant poly
        PolyL.toSlices polynomial `shouldBe` fmap (second ((-1) *)) (PolyL.toSlices poly)
        PolyL.polyRefs polynomial `shouldBe` fmap negate (PolyL.polyRefs poly)
        PolyL.validate polynomial `shouldBe` Nothing