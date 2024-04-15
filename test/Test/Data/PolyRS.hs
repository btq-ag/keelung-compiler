{-# LANGUAGE DataKinds #-}

-- | Polynomial of References and Slices
module Test.Data.PolyRS (tests, run) where

import Data.Bifunctor (second)
import Data.Field.Galois (Prime)
import Data.Map (Map)
import Data.Map qualified as Map
import Keelung.Data.Limb (Limb)
import Keelung.Data.Limb qualified as Limb
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

toLimbMap :: (Integral n) => [(Limb, n)] -> Map Limb n
toLimbMap = Map.filterWithKey (\limb n -> not (Limb.null limb) && n /= 0) . Map.fromListWith (+)

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
  --            expected: SlicePoly {unSlicePoly = fromList [(U₁₁9,[P (5 `modulo` 17)$6]),(U₁₄4,[P (4 `modulo` 17)($12 ~ $13)]),(U₁₅5,[P (11 `modulo` 17)($13 ~ $14)]),(U₁₇7,[P (16 `modulo` 17)$11]),(U₁₈5,[P (11 `modulo` 17)($12 ~ $14)]),(U₂₁10,[P (2 `modulo` 17)($1 ~ $7), P (15 `modulo` 17)$13]),(U₂₁2,[P (4 `modulo` 17)($8 ~ $15)]),(U₂₅2,[P (14 `modulo` 17)($15 ~ $17)]),(U₂₆1,[P (8 `modulo` 17)($14 ~ $21)]),(U₂₇9,[P (16 `modulo` 17)($9 ~ $11)]),(U₂₈8,[P (7 `modulo` 17)($14 ~ $15)]),(U₂₉10,[P (2 `modulo` 17)($12 ~ $19)]),(U₂₉4,[$7 ~ $13]),(U₃₁2,[P (10 `modulo` 17)($15 ~ $21)]),(UO₁₈1,[$8 ~ $14]),(UO₁₉1,[P (14 `modulo` 17)($5 ~ $8)]),(UO₂₀7,[P (12 `modulo` 17)($7 ~ $11)]),(UO₂₂3,[P (3 `modulo` 17)($15 ~ $21)]),(UO₂₂1,[$6 ~ $10]),(UO₂₃9,[P (3 `modulo` 17)($11 ~ $17)]),(UO₂₃4,[P (16 `modulo` 17)($13 ~ $14)]),(UO₂₄4,[P (3 `modulo` 17)($15 ~ $19)]),(UO₂₅8,[P (2 `modulo` 17)($13 ~ $16)]),(UO₂₅4,[P (16 `modulo` 17)$13]),(UO₂₅2,[P (6 `modulo` 17)$8, P (11 `modulo` 17)($10 ~ $11)]),(UO₂₆10,[$9]),(UO₂₆9,[]),(UO₂₆8,[P (4 `modulo` 17)($12 ~ $17)]),(UI₁₀4,[P (12 `modulo` 17)($5 ~ $9)]),(UI₁₅2,[P (12 `modulo` 17)($3 ~ $7)]),(UI₁₆7,[P (15 `modulo` 17)$11]),(UI₁₆4,[P (15 `modulo` 17)$15]),(UP₁₇4,[P (14 `modulo` 17)$11]),(UP₁₇1,[P (16 `modulo` 17)($7 ~ $11)]),(UP₁₇0,[P (2 `modulo` 17)($4 ~ $6)]),(UI₁₈6,[$4]),(UI₁₉6,[P (5 `modulo` 17)($4 ~ $8)]),(UP₁₉1,[P (9 `modulo` 17)$7]),(UI₂₁4,[P (9 `modulo` 17)($8 ~ $11)]),(UP₂₅10,[P (15 `modulo` 17)($9 ~ $13)]),(UP₂₅5,[P (16 `modulo` 17)($4 ~ $9)]),(UI₂₅0,[P (13 `modulo` 17)($6 ~ $11)]),(UI₂₇5,[P (13 `modulo` 17)($12 ~ $18)]),(UP₃₁1,[P (6 `modulo` 17)($14 ~ $19)]),(UP₃₂9,[P (10 `modulo` 17)($13 ~ $20)]),(UP₃₄7,[P (9 `modulo` 17)($15 ~ $17)]),(UI₃₇9,[P (7 `modulo` 17)($16 ~ $20)])]}
  --            but got: SlicePoly {unSlicePoly = fromList [(U₁₁9,[P (5 `modulo` 17)$6]),(U₁₄4,[P (4 `modulo` 17)($12 ~ $13)]),(U₁₅5,[P (11 `modulo` 17)($13 ~ $14)]),(U₁₇7,[P (16 `modulo` 17)$11]),(U₁₈5,[P (11 `modulo` 17)($12 ~ $14)]),(U₂₁10,[P (2 `modulo` 17)($1 ~ $7), P (15 `modulo` 17)$13]),(U₂₁2,[P (4 `modulo` 17)($8 ~ $15)]),(U₂₅2,[P (14 `modulo` 17)($15 ~ $17)]),(U₂₆1,[P (8 `modulo` 17)($14 ~ $21)]),(U₂₇9,[P (16 `modulo` 17)($9 ~ $11)]),(U₂₈8,[P (7 `modulo` 17)($14 ~ $15)]),(U₂₉10,[P (2 `modulo` 17)($12 ~ $19)]),(U₂₉4,[$7 ~ $13]),(U₃₁2,[P (10 `modulo` 17)($15 ~ $21)]),(UO₁₈1,[$8 ~ $14]),(UO₁₉1,[P (14 `modulo` 17)($5 ~ $8)]),(UO₂₀7,[P (12 `modulo` 17)($7 ~ $11)]),(UO₂₂3,[P (3 `modulo` 17)($15 ~ $21)]),(UO₂₂1,[$6 ~ $10]),(UO₂₃9,[P (3 `modulo` 17)($11 ~ $17)]),(UO₂₃4,[P (16 `modulo` 17)($13 ~ $14)]),(UO₂₄4,[P (3 `modulo` 17)($15 ~ $19)]),(UO₂₅8,[P (2 `modulo` 17)($13 ~ $16)]),(UO₂₅4,[P (16 `modulo` 17)$13]),(UO₂₅2,[P (6 `modulo` 17)$8, P (11 `modulo` 17)($10 ~ $11)]),(UO₂₆10,[$9]),(UO₂₆8,[P (4 `modulo` 17)($12 ~ $17)]),(UI₁₀4,[P (12 `modulo` 17)($5 ~ $9)]),(UI₁₅2,[P (12 `modulo` 17)($3 ~ $7)]),(UI₁₆7,[P (15 `modulo` 17)$11]),(UI₁₆4,[P (15 `modulo` 17)$15]),(UP₁₇4,[P (14 `modulo` 17)$11]),(UP₁₇1,[P (16 `modulo` 17)($7 ~ $11)]),(UP₁₇0,[P (2 `modulo` 17)($4 ~ $6)]),(UI₁₈6,[$4]),(UI₁₉6,[P (5 `modulo` 17)($4 ~ $8)]),(UP₁₉1,[P (9 `modulo` 17)$7]),(UI₂₁4,[P (9 `modulo` 17)($8 ~ $11)]),(UP₂₅10,[P (15 `modulo` 17)($9 ~ $13)]),(UP₂₅5,[P (16 `modulo` 17)($4 ~ $9)]),(UI₂₅0,[P (13 `modulo` 17)($6 ~ $11)]),(UI₂₇5,[P (13 `modulo` 17)($12 ~ $18)]),(UP₃₁1,[P (6 `modulo` 17)($14 ~ $19)]),(UP₃₂9,[P (10 `modulo` 17)($13 ~ $20)]),(UP₃₄7,[P (9 `modulo` 17)($15 ~ $17)]),(UI₃₇9,[P (7 `modulo` 17)($16 ~ $20)])]}
  --          (P (11 `modulo` 17) + P (10 `modulo` 17)FO0 + P (7 `modulo` 17)FO1 + P (13 `modulo` 17)FI3 + P (6 `modulo` 17)FP1 + P (11 `modulo` 17)FP3 + P (3 `modulo` 17)FP5 - F0 + P (4 `modulo` 17)F3 + P (4 `modulo` 17)BI3 + P (10 `modulo` 17)BP1 + P (6 `modulo` 17)BP4 + P (2 `modulo` 17)U₉2[0:6] + P (9 `modulo` 17)U₁₀5[7:8] + U₁₀1[1:8] + U₁₃5[2:8] + P (6 `modulo` 17)U₁₇5[6:14] - UO₁0[0:1] + P (3 `modulo` 17)UO₂3[0:1] + P (13 `modulo` 17)UO₈4[3:4] - UO₁₂3[3:5] + P (10 `modulo` 17)UO₁₂0[3:8] + P (14 `modulo` 17)UO₁₄1[4:8] + P (6 `modulo` 17)UO₁₆0[1:9] + P (7 `modulo` 17)UO₁₇1[7:12] + P (14 `modulo` 17)UO₂₁4[8:14] + P (12 `modulo` 17)UI₅1[0:2] + P (13 `modulo` 17)UP₆2[2:5] - UI₆0[0:1] + P (3 `modulo` 17)UP₈2[2:6] + P (7 `modulo` 17)UP₁₂5[2:7] + P (14 `modulo` 17)UI₁₂4[4:10] + P (7 `modulo` 17)UP₁₂2[1:5] + P (2 `modulo` 17)UP₁₃2[5:9] + P (3 `modulo` 17)UP₁₃1[7:12] + P (12 `modulo` 17)UI₁₄3[8:9] + P (15 `modulo` 17)UI₁₇4[7:9] + P (7 `modulo` 17)UP₁₈1[5:10] + P (5 `modulo` 17)UP₂₃0[8:16],P (3 `modulo` 17) - FO0 + P (6 `modulo` 17)FO1 + P (7 `modulo` 17)FO3 + P (15 `modulo` 17)FO4 + P (3 `modulo` 17)FO5 + P (6 `modulo` 17)FI0 + P (14 `modulo` 17)FI3 + P (4 `modulo` 17)FI4 + P (4 `modulo` 17)FI5 + P (5 `modulo` 17)FP1 + P (2 `modulo` 17)FP2 + P (8 `modulo` 17)FP3 + FP4 + P (15 `modulo` 17)FP5 + P (4 `modulo` 17)F0 + F3 + P (4 `modulo` 17)F4 + P (5 `modulo` 17)F5 + P (5 `modulo` 17)BO2 + P (2 `modulo` 17)BI0 + P (8 `modulo` 17)BI3 + P (9 `modulo` 17)BI4 + P (13 `modulo` 17)BP1 + P (6 `modulo` 17)BP2 - BP3 + P (13 `modulo` 17)BP5 + P (7 `modulo` 17)U₈4[1:6] + P (13 `modulo` 17)U₉4[4:9] + P (10 `modulo` 17)U₉3[4:5] + P (13 `modulo` 17)U₉1[4:9] + P (8 `modulo` 17)U₁₀5[5:9] - U₁₃4[3:5] - U₁₃4[5:10] + P (11 `modulo` 17)U₁₃4[10:12] + P (15 `modulo` 17)U₁₄2[6:11] + P (10 `modulo` 17)U₁₅4[3:9] + P (5 `modulo` 17)U₁₆5[3:11] + P (12 `modulo` 17)U₂₂4[6:14] + P (14 `modulo` 17)UO₂3[0:1] + P (7 `modulo` 17)UO₉2[8:9] + P (13 `modulo` 17)UO₁₀2[6:9] + P (6 `modulo` 17)UO₁₀1[0:5] + P (5 `modulo` 17)UO₁₁2[5:6] + P (14 `modulo` 17)UO₁₅3[4:6] - UO₁₅3[6:11] + P (15 `modulo` 17)UO₁₇0[8:14] + P (4 `modulo` 17)UO₁₈4[7:13] + P (6 `modulo` 17)UO₂₁0[8:15] + P (6 `modulo` 17)UI₂1[0:1] + UI₃2[0:3] - UP₇5[1:7] + P (14 `modulo` 17)UI₈5[3:4] + P (9 `modulo` 17)UI₉0[5:8] + P (4 `modulo` 17)UI₁₂0[3:9] + P (14 `modulo` 17)UI₁₃3[0:5] + UP₁₃1[2:7] + P (8 `modulo` 17)UP₁₄3[1:6] + P (6 `modulo` 17)UI₁₄2[3:9] + P (9 `modulo` 17)UI₁₅5[5:13] + P (10 `modulo` 17)UI₁₅2[6:9] + P (14 `modulo` 17)UP₁₆2[5:8] + P (8 `modulo` 17)UP₁₇4[5:9] + P (14 `modulo` 17)UI₁₇0[3:11] + P (15 `modulo` 17)UP₁₈5[6:14])
  --            expected: SlicePoly {unSlicePoly = fromList [(U₈4,[P (7 `modulo` 17)($1 ~ $5)]),(U₉4,[P (13 `modulo` 17)($4 ~ $8)]),(U₉3,[P (10 `modulo` 17)$4]),(U₉2,[P (2 `modulo` 17)($0 ~ $5)]),(U₉1,[P (13 `modulo` 17)($4 ~ $8)]),(U₁₀5,[P (8 `modulo` 17)($5 ~ $6), P (6 `modulo` 17)$7, P (8 `modulo` 17)$8]),(U₁₀1,[$1 ~ $7]),(U₁₃5,[$2 ~ $7]),(U₁₃4,[P (16 `modulo` 17)($3 ~ $4), P (4 `modulo` 17)($5 ~ $9), P (5 `modulo` 17)($10 ~ $11)]),(U₁₄2,[P (15 `modulo` 17)($6 ~ $10)]),(U₁₅4,[P (10 `modulo` 17)($3 ~ $8)]),(U₁₆5,[P (5 `modulo` 17)($3 ~ $10)]),(U₁₇5,[P (6 `modulo` 17)($6 ~ $13)]),(U₂₂4,[P (12 `modulo` 17)($6 ~ $13)]),(UO₁0,[P (16 `modulo` 17)$0]),(UO₂3,[]),(UO₈4,[P (13 `modulo` 17)$3]),(UO₉2,[P (7 `modulo` 17)$8]),(UO₁₀2,[P (13 `modulo` 17)($6 ~ $8)]),(UO₁₀1,[P (6 `modulo` 17)($0 ~ $4)]),(UO₁₁2,[P (5 `modulo` 17)$5]),(UO₁₂3,[P (16 `modulo` 17)($3 ~ $4)]),(UO₁₂0,[P (10 `modulo` 17)($3 ~ $7)]),(UO₁₄1,[P (14 `modulo` 17)($4 ~ $7)]),(UO₁₅3,[P (14 `modulo` 17)($4 ~ $5), P (4 `modulo` 17)($6 ~ $10)]),(UO₁₆0,[P (6 `modulo` 17)($1 ~ $8)]),(UO₁₇1,[P (7 `modulo` 17)($7 ~ $11)]),(UO₁₇0,[P (15 `modulo` 17)($8 ~ $13)]),(UO₁₈4,[P (4 `modulo` 17)($7 ~ $12)]),(UO₂₁4,[P (14 `modulo` 17)($8 ~ $13)]),(UO₂₁0,[P (6 `modulo` 17)($8 ~ $14)]),(UI₂1,[P (6 `modulo` 17)$0]),(UI₃2,[$0 ~ $2]),(UI₅1,[P (12 `modulo` 17)($0 ~ $1)]),(UP₆2,[P (13 `modulo` 17)($2 ~ $4)]),(UI₆0,[P (16 `modulo` 17)$0]),(UP₇5,[P (16 `modulo` 17)($1 ~ $6)]),(UI₈5,[P (14 `modulo` 17)$3]),(UP₈2,[P (3 `modulo` 17)($2 ~ $5)]),(UI₉0,[P (9 `modulo` 17)($5 ~ $7)]),(UP₁₂5,[P (7 `modulo` 17)($2 ~ $6)]),(UI₁₂4,[P (14 `modulo` 17)($4 ~ $9)]),(UP₁₂2,[P (7 `modulo` 17)($1 ~ $4)]),(UI₁₂0,[P (4 `modulo` 17)($3 ~ $8)]),(UI₁₃3,[P (14 `modulo` 17)($0 ~ $4)]),(UP₁₃2,[P (2 `modulo` 17)($5 ~ $8)]),(UP₁₃1,[$2 ~ $6, P (7 `modulo` 17)($7 ~ $11)]),(UP₁₄3,[P (8 `modulo` 17)($1 ~ $5)]),(UI₁₄3,[P (12 `modulo` 17)$8]),(UI₁₄2,[P (6 `modulo` 17)($3 ~ $8)]),(UI₁₅5,[P (9 `modulo` 17)($5 ~ $12)]),(UI₁₅2,[P (10 `modulo` 17)($6 ~ $8)]),(UP₁₆2,[P (14 `modulo` 17)($5 ~ $7)]),(UP₁₇4,[P (8 `modulo` 17)($5 ~ $8)]),(UI₁₇4,[P (15 `modulo` 17)($7 ~ $8)]),(UI₁₇0,[P (14 `modulo` 17)($3 ~ $10)]),(UP₁₈5,[P (15 `modulo` 17)($6 ~ $13)]),(UP₁₈1,[P (7 `modulo` 17)($5 ~ $9)]),(UP₂₃0,[P (5 `modulo` 17)($8 ~ $15)])]}
  --            but got: SlicePoly {unSlicePoly = fromList [(U₈4,[P (7 `modulo` 17)($1 ~ $5)]),(U₉4,[P (13 `modulo` 17)($4 ~ $8)]),(U₉3,[P (10 `modulo` 17)$4]),(U₉2,[P (2 `modulo` 17)($0 ~ $5)]),(U₉1,[P (13 `modulo` 17)($4 ~ $8)]),(U₁₀5,[P (8 `modulo` 17)($5 ~ $6), P (6 `modulo` 17)$7, P (8 `modulo` 17)$8]),(U₁₀1,[$1 ~ $7]),(U₁₃5,[$2 ~ $7]),(U₁₃4,[P (16 `modulo` 17)($3 ~ $4), P (4 `modulo` 17)($5 ~ $9), P (5 `modulo` 17)($10 ~ $11)]),(U₁₄2,[P (15 `modulo` 17)($6 ~ $10)]),(U₁₅4,[P (10 `modulo` 17)($3 ~ $8)]),(U₁₆5,[P (5 `modulo` 17)($3 ~ $10)]),(U₁₇5,[P (6 `modulo` 17)($6 ~ $13)]),(U₂₂4,[P (12 `modulo` 17)($6 ~ $13)]),(UO₁0,[P (16 `modulo` 17)$0]),(UO₈4,[P (13 `modulo` 17)$3]),(UO₉2,[P (7 `modulo` 17)$8]),(UO₁₀2,[P (13 `modulo` 17)($6 ~ $8)]),(UO₁₀1,[P (6 `modulo` 17)($0 ~ $4)]),(UO₁₁2,[P (5 `modulo` 17)$5]),(UO₁₂3,[P (16 `modulo` 17)($3 ~ $4)]),(UO₁₂0,[P (10 `modulo` 17)($3 ~ $7)]),(UO₁₄1,[P (14 `modulo` 17)($4 ~ $7)]),(UO₁₅3,[P (14 `modulo` 17)($4 ~ $5), P (4 `modulo` 17)($6 ~ $10)]),(UO₁₆0,[P (6 `modulo` 17)($1 ~ $8)]),(UO₁₇1,[P (7 `modulo` 17)($7 ~ $11)]),(UO₁₇0,[P (15 `modulo` 17)($8 ~ $13)]),(UO₁₈4,[P (4 `modulo` 17)($7 ~ $12)]),(UO₂₁4,[P (14 `modulo` 17)($8 ~ $13)]),(UO₂₁0,[P (6 `modulo` 17)($8 ~ $14)]),(UI₂1,[P (6 `modulo` 17)$0]),(UI₃2,[$0 ~ $2]),(UI₅1,[P (12 `modulo` 17)($0 ~ $1)]),(UP₆2,[P (13 `modulo` 17)($2 ~ $4)]),(UI₆0,[P (16 `modulo` 17)$0]),(UP₇5,[P (16 `modulo` 17)($1 ~ $6)]),(UI₈5,[P (14 `modulo` 17)$3]),(UP₈2,[P (3 `modulo` 17)($2 ~ $5)]),(UI₉0,[P (9 `modulo` 17)($5 ~ $7)]),(UP₁₂5,[P (7 `modulo` 17)($2 ~ $6)]),(UI₁₂4,[P (14 `modulo` 17)($4 ~ $9)]),(UP₁₂2,[P (7 `modulo` 17)($1 ~ $4)]),(UI₁₂0,[P (4 `modulo` 17)($3 ~ $8)]),(UI₁₃3,[P (14 `modulo` 17)($0 ~ $4)]),(UP₁₃2,[P (2 `modulo` 17)($5 ~ $8)]),(UP₁₃1,[$2 ~ $6, P (7 `modulo` 17)($7 ~ $11)]),(UP₁₄3,[P (8 `modulo` 17)($1 ~ $5)]),(UI₁₄3,[P (12 `modulo` 17)$8]),(UI₁₄2,[P (6 `modulo` 17)($3 ~ $8)]),(UI₁₅5,[P (9 `modulo` 17)($5 ~ $12)]),(UI₁₅2,[P (10 `modulo` 17)($6 ~ $8)]),(UP₁₆2,[P (14 `modulo` 17)($5 ~ $7)]),(UP₁₇4,[P (8 `modulo` 17)($5 ~ $8)]),(UI₁₇4,[P (15 `modulo` 17)($7 ~ $8)]),(UI₁₇0,[P (14 `modulo` 17)($3 ~ $10)]),(UP₁₈5,[P (15 `modulo` 17)($6 ~ $13)]),(UP₁₈1,[P (7 `modulo` 17)($5 ~ $9)]),(UP₂₃0,[P (5 `modulo` 17)($8 ~ $15)])]}
  --          (P (3 `modulo` 17) + P (8 `modulo` 17)FO0 + P (5 `modulo` 17)FO1 + P (14 `modulo` 17)FO2 - FO4 + P (3 `modulo` 17)FO5 + P (9 `modulo` 17)FI0 + P (7 `modulo` 17)FI2 + P (9 `modulo` 17)FI3 + P (11 `modulo` 17)FI4 + P (7 `modulo` 17)FI5 + P (9 `modulo` 17)FP0 + P (5 `modulo` 17)FP1 + P (13 `modulo` 17)FP2 + P (15 `modulo` 17)FP3 + P (9 `modulo` 17)FP4 + FP5 + P (12 `modulo` 17)F0 + P (15 `modulo` 17)F2 + P (3 `modulo` 17)F3 + P (12 `modulo` 17)F4 + P (13 `modulo` 17)BO1 + P (9 `modulo` 17)BO2 + P (14 `modulo` 17)BI2 + P (3 `modulo` 17)BI3 + P (10 `modulo` 17)BI4 + P (6 `modulo` 17)BI5 + P (7 `modulo` 17)BP0 + P (13 `modulo` 17)BP1 + P (4 `modulo` 17)BP2 + P (4 `modulo` 17)BP4 + P (3 `modulo` 17)BP5 + P (9 `modulo` 17)B0 + P (15 `modulo` 17)B2 + B3 + P (12 `modulo` 17)B4 + P (4 `modulo` 17)B5 - U₉3[2:5] + P (12 `modulo` 17)U₁₃3[6:13] + P (13 `modulo` 17)U₁₇3[7:9] + P (12 `modulo` 17)U₁₉3[6:11] + P (9 `modulo` 17)UO₁₃4[4:12] + P (2 `modulo` 17)UO₁₅0[6:7] - UP₁₁5[3:4] + P (7 `modulo` 17)UP₁₁0[8:9] + P (10 `modulo` 17)UI₂₀1[6:12],P (4 `modulo` 17) + FO0 + P (6 `modulo` 17)FO1 + P (8 `modulo` 17)F1 + P (7 `modulo` 17)F2 + P (10 `modulo` 17)F4 + P (6 `modulo` 17)F5 - BO1 + P (12 `modulo` 17)BO2 + P (15 `modulo` 17)BI0 + P (13 `modulo` 17)BI3 + BP0 - BP1 + BP4 + P (7 `modulo` 17)U₂2[0:2] + P (5 `modulo` 17)U₂1[1:2] + P (6 `modulo` 17)U₃1[0:3] + P (4 `modulo` 17)U₄1[2:4] + P (6 `modulo` 17)U₄0[0:3] + P (8 `modulo` 17)U₈1[2:7] + P (7 `modulo` 17)U₁₁5[2:6] + P (5 `modulo` 17)U₁₁5[6:8] + P (2 `modulo` 17)U₁₁3[5:7] + P (13 `modulo` 17)U₁₂4[5:8] + P (10 `modulo` 17)U₁₂2[6:12] + P (11 `modulo` 17)U₁₄0[6:12] + P (14 `modulo` 17)U₁₅4[3:7] + P (9 `modulo` 17)U₁₅4[7:10] + P (14 `modulo` 17)U₁₅4[10:13] + P (11 `modulo` 17)U₁₆5[8:13] + P (15 `modulo` 17)U₁₇4[4:12] + P (8 `modulo` 17)U₁₇3[8:14] + P (10 `modulo` 17)U₁₇2[7:15] + P (8 `modulo` 17)U₁₉5[7:13] + P (14 `modulo` 17)U₁₉4[4:11] + P (13 `modulo` 17)U₂₁2[7:15] + P (7 `modulo` 17)U₂₂3[8:14] + P (7 `modulo` 17)UO₅5[2:5] + P (2 `modulo` 17)UO₆3[3:4] + P (7 `modulo` 17)UO₇5[1:6] + P (3 `modulo` 17)UO₉5[4:6] + P (3 `modulo` 17)UO₉3[2:9] + P (10 `modulo` 17)UO₁₁0[3:8] + P (9 `modulo` 17)UO₁₂4[5:12] + P (10 `modulo` 17)UO₁₂3[6:8] + P (7 `modulo` 17)UO₁₅5[6:11] + P (10 `modulo` 17)UO₁₆0[8:11] + P (6 `modulo` 17)UO₁₇5[7:15] + UO₂₁1[6:14] + P (9 `modulo` 17)UI₃0[0:2] + P (14 `modulo` 17)UI₆5[3:6] + P (6 `modulo` 17)UI₇5[2:3] + P (3 `modulo` 17)UI₇5[3:4] - UI₇5[4:6] - UI₇2[1:6] + P (12 `modulo` 17)UP₇0[3:6] + P (15 `modulo` 17)UP₈5[4:6] + P (14 `modulo` 17)UP₉5[0:3] + P (4 `modulo` 17)UP₉5[3:7] + P (6 `modulo` 17)UP₉5[7:9] + P (13 `modulo` 17)UP₉4[6:9] + P (12 `modulo` 17)UI₉4[0:6] + P (15 `modulo` 17)UI₉0[5:8] + P (2 `modulo` 17)UP₁₀5[4:5] + P (8 `modulo` 17)UP₁₀5[5:7] + P (6 `modulo` 17)UP₁₀4[1:6] + P (5 `modulo` 17)UI₁₀4[4:9] + UP₁₁5[3:4] + P (12 `modulo` 17)UP₁₁2[7:10] + P (10 `modulo` 17)UP₁₃4[6:7] + P (12 `modulo` 17)UP₁₃3[6:10] - UP₁₄5[6:13] + P (13 `modulo` 17)UP₁₄3[6:9] + P (15 `modulo` 17)UP₁₄2[4:7] + UP₁₄0[6:7] + P (6 `modulo` 17)UI₁₅5[7:14] + P (6 `modulo` 17)UI₁₅4[3:8] + P (14 `modulo` 17)UI₁₅4[8:10] + P (4 `modulo` 17)UP₁₅3[2:5] + P (4 `modulo` 17)UP₁₅3[5:10] + P (5 `modulo` 17)UP₁₅3[10:11] + P (12 `modulo` 17)UP₁₅2[3:9] + P (10 `modulo` 17)UI₁₅1[2:3] + P (12 `modulo` 17)UI₁₅1[3:8] + P (3 `modulo` 17)UI₁₇2[8:12] + P (3 `modulo` 17)UP₁₈2[6:8] + P (14 `modulo` 17)UP₁₈2[14:16] + P (9 `modulo` 17)UI₁₉3[7:14] + P (15 `modulo` 17)UI₂₄0[8:16])
  --            expected: SlicePoly {unSlicePoly = fromList [(U₂2,[P (7 `modulo` 17)($0 ~ $1)]),(U₂1,[P (5 `modulo` 17)$1]),(U₃1,[P (6 `modulo` 17)($0 ~ $2)]),(U₄1,[P (4 `modulo` 17)($2 ~ $3)]),(U₄0,[P (6 `modulo` 17)($0 ~ $2)]),(U₈1,[P (8 `modulo` 17)($2 ~ $6)]),(U₉3,[P (16 `modulo` 17)($2 ~ $4)]),(U₁₁5,[P (7 `modulo` 17)($2 ~ $5), P (12 `modulo` 17)($6 ~ $7)]),(U₁₁3,[P (2 `modulo` 17)($5 ~ $6)]),(U₁₂4,[P (13 `modulo` 17)($5 ~ $7)]),(U₁₂2,[P (10 `modulo` 17)($6 ~ $11)]),(U₁₃3,[P (12 `modulo` 17)($6 ~ $12)]),(U₁₄0,[P (11 `modulo` 17)($6 ~ $11)]),(U₁₅4,[P (14 `modulo` 17)($3 ~ $6), P (8 `modulo` 17)($7 ~ $9), P (11 `modulo` 17)($10 ~ $12)]),(U₁₆5,[P (11 `modulo` 17)($8 ~ $12)]),(U₁₇4,[P (15 `modulo` 17)($4 ~ $11)]),(U₁₇3,[P (13 `modulo` 17)$7, P (4 `modulo` 17)($9 ~ $13)]),(U₁₇2,[P (10 `modulo` 17)($7 ~ $14)]),(U₁₉5,[P (8 `modulo` 17)($7 ~ $12)]),(U₁₉4,[P (14 `modulo` 17)($4 ~ $10)]),(U₁₉3,[P (12 `modulo` 17)($6 ~ $10)]),(U₂₁2,[P (13 `modulo` 17)($7 ~ $14)]),(U₂₂3,[P (7 `modulo` 17)($8 ~ $13)]),(UO₅5,[P (7 `modulo` 17)($2 ~ $4)]),(UO₆3,[P (2 `modulo` 17)$3]),(UO₇5,[P (7 `modulo` 17)($1 ~ $5)]),(UO₉5,[P (3 `modulo` 17)($4 ~ $5)]),(UO₉3,[P (3 `modulo` 17)($2 ~ $8)]),(UO₁₁0,[P (10 `modulo` 17)($3 ~ $7)]),(UO₁₂4,[P (9 `modulo` 17)($5 ~ $11)]),(UO₁₂3,[P (10 `modulo` 17)($6 ~ $7)]),(UO₁₃4,[P (9 `modulo` 17)($4 ~ $11)]),(UO₁₅5,[P (7 `modulo` 17)($6 ~ $10)]),(UO₁₅0,[P (2 `modulo` 17)$6]),(UO₁₆0,[P (10 `modulo` 17)($8 ~ $10)]),(UO₁₇5,[P (6 `modulo` 17)($7 ~ $14)]),(UO₂₁1,[$6 ~ $13]),(UI₃0,[P (9 `modulo` 17)($0 ~ $1)]),(UI₆5,[P (14 `modulo` 17)($3 ~ $5)]),(UI₇5,[P (6 `modulo` 17)$2, P (10 `modulo` 17)$3, P (4 `modulo` 17)($4 ~ $5)]),(UI₇2,[P (16 `modulo` 17)($1 ~ $5)]),(UP₇0,[P (12 `modulo` 17)($3 ~ $5)]),(UP₈5,[P (15 `modulo` 17)($4 ~ $5)]),(UP₉5,[P (14 `modulo` 17)($0 ~ $2), P (9 `modulo` 17)($3 ~ $6), P (12 `modulo` 17)($7 ~ $8)]),(UP₉4,[P (13 `modulo` 17)($6 ~ $8)]),(UI₉4,[P (12 `modulo` 17)($0 ~ $5)]),(UI₉0,[P (15 `modulo` 17)($5 ~ $7)]),(UP₁₀5,[P (2 `modulo` 17)$4, P (4 `modulo` 17)($5 ~ $6)]),(UP₁₀4,[P (6 `modulo` 17)($1 ~ $5)]),(UI₁₀4,[P (5 `modulo` 17)($4 ~ $8)]),(UP₁₁5,[]),(UP₁₁2,[P (12 `modulo` 17)($7 ~ $9)]),(UP₁₁0,[P (7 `modulo` 17)$8]),(UP₁₃4,[P (10 `modulo` 17)$6]),(UP₁₃3,[P (12 `modulo` 17)($6 ~ $9)]),(UP₁₄5,[P (16 `modulo` 17)($6 ~ $12)]),(UP₁₄3,[P (13 `modulo` 17)($6 ~ $8)]),(UP₁₄2,[P (15 `modulo` 17)($4 ~ $6)]),(UP₁₄0,[$6]),(UI₁₅5,[P (6 `modulo` 17)($7 ~ $13)]),(UI₁₅4,[P (6 `modulo` 17)($3 ~ $7), P (10 `modulo` 17)($8 ~ $9)]),(UP₁₅3,[P (4 `modulo` 17)($2 ~ $4), P (9 `modulo` 17)($5 ~ $9), P (5 `modulo` 17)$10]),(UP₁₅2,[P (12 `modulo` 17)($3 ~ $8)]),(UI₁₅1,[P (10 `modulo` 17)$2, P (6 `modulo` 17)($3 ~ $7)]),(UI₁₇2,[P (3 `modulo` 17)($8 ~ $11)]),(UP₁₈2,[P (3 `modulo` 17)($6 ~ $7), P (14 `modulo` 17)($14 ~ $15)]),(UI₁₉3,[P (9 `modulo` 17)($7 ~ $13)]),(UI₂₀1,[P (10 `modulo` 17)($6 ~ $11)]),(UI₂₄0,[P (15 `modulo` 17)($8 ~ $15)])]}
  --            but got: SlicePoly {unSlicePoly = fromList [(U₂2,[P (7 `modulo` 17)($0 ~ $1)]),(U₂1,[P (5 `modulo` 17)$1]),(U₃1,[P (6 `modulo` 17)($0 ~ $2)]),(U₄1,[P (4 `modulo` 17)($2 ~ $3)]),(U₄0,[P (6 `modulo` 17)($0 ~ $2)]),(U₈1,[P (8 `modulo` 17)($2 ~ $6)]),(U₉3,[P (16 `modulo` 17)($2 ~ $4)]),(U₁₁5,[P (7 `modulo` 17)($2 ~ $5), P (12 `modulo` 17)($6 ~ $7)]),(U₁₁3,[P (2 `modulo` 17)($5 ~ $6)]),(U₁₂4,[P (13 `modulo` 17)($5 ~ $7)]),(U₁₂2,[P (10 `modulo` 17)($6 ~ $11)]),(U₁₃3,[P (12 `modulo` 17)($6 ~ $12)]),(U₁₄0,[P (11 `modulo` 17)($6 ~ $11)]),(U₁₅4,[P (14 `modulo` 17)($3 ~ $6), P (8 `modulo` 17)($7 ~ $9), P (11 `modulo` 17)($10 ~ $12)]),(U₁₆5,[P (11 `modulo` 17)($8 ~ $12)]),(U₁₇4,[P (15 `modulo` 17)($4 ~ $11)]),(U₁₇3,[P (13 `modulo` 17)$7, P (4 `modulo` 17)($9 ~ $13)]),(U₁₇2,[P (10 `modulo` 17)($7 ~ $14)]),(U₁₉5,[P (8 `modulo` 17)($7 ~ $12)]),(U₁₉4,[P (14 `modulo` 17)($4 ~ $10)]),(U₁₉3,[P (12 `modulo` 17)($6 ~ $10)]),(U₂₁2,[P (13 `modulo` 17)($7 ~ $14)]),(U₂₂3,[P (7 `modulo` 17)($8 ~ $13)]),(UO₅5,[P (7 `modulo` 17)($2 ~ $4)]),(UO₆3,[P (2 `modulo` 17)$3]),(UO₇5,[P (7 `modulo` 17)($1 ~ $5)]),(UO₉5,[P (3 `modulo` 17)($4 ~ $5)]),(UO₉3,[P (3 `modulo` 17)($2 ~ $8)]),(UO₁₁0,[P (10 `modulo` 17)($3 ~ $7)]),(UO₁₂4,[P (9 `modulo` 17)($5 ~ $11)]),(UO₁₂3,[P (10 `modulo` 17)($6 ~ $7)]),(UO₁₃4,[P (9 `modulo` 17)($4 ~ $11)]),(UO₁₅5,[P (7 `modulo` 17)($6 ~ $10)]),(UO₁₅0,[P (2 `modulo` 17)$6]),(UO₁₆0,[P (10 `modulo` 17)($8 ~ $10)]),(UO₁₇5,[P (6 `modulo` 17)($7 ~ $14)]),(UO₂₁1,[$6 ~ $13]),(UI₃0,[P (9 `modulo` 17)($0 ~ $1)]),(UI₆5,[P (14 `modulo` 17)($3 ~ $5)]),(UI₇5,[P (6 `modulo` 17)$2, P (10 `modulo` 17)$3, P (4 `modulo` 17)($4 ~ $5)]),(UI₇2,[P (16 `modulo` 17)($1 ~ $5)]),(UP₇0,[P (12 `modulo` 17)($3 ~ $5)]),(UP₈5,[P (15 `modulo` 17)($4 ~ $5)]),(UP₉5,[P (14 `modulo` 17)($0 ~ $2), P (9 `modulo` 17)($3 ~ $6), P (12 `modulo` 17)($7 ~ $8)]),(UP₉4,[P (13 `modulo` 17)($6 ~ $8)]),(UI₉4,[P (12 `modulo` 17)($0 ~ $5)]),(UI₉0,[P (15 `modulo` 17)($5 ~ $7)]),(UP₁₀5,[P (2 `modulo` 17)$4, P (4 `modulo` 17)($5 ~ $6)]),(UP₁₀4,[P (6 `modulo` 17)($1 ~ $5)]),(UI₁₀4,[P (5 `modulo` 17)($4 ~ $8)]),(UP₁₁2,[P (12 `modulo` 17)($7 ~ $9)]),(UP₁₁0,[P (7 `modulo` 17)$8]),(UP₁₃4,[P (10 `modulo` 17)$6]),(UP₁₃3,[P (12 `modulo` 17)($6 ~ $9)]),(UP₁₄5,[P (16 `modulo` 17)($6 ~ $12)]),(UP₁₄3,[P (13 `modulo` 17)($6 ~ $8)]),(UP₁₄2,[P (15 `modulo` 17)($4 ~ $6)]),(UP₁₄0,[$6]),(UI₁₅5,[P (6 `modulo` 17)($7 ~ $13)]),(UI₁₅4,[P (6 `modulo` 17)($3 ~ $7), P (10 `modulo` 17)($8 ~ $9)]),(UP₁₅3,[P (4 `modulo` 17)($2 ~ $4), P (9 `modulo` 17)($5 ~ $9), P (5 `modulo` 17)$10]),(UP₁₅2,[P (12 `modulo` 17)($3 ~ $8)]),(UI₁₅1,[P (10 `modulo` 17)$2, P (6 `modulo` 17)($3 ~ $7)]),(UI₁₇2,[P (3 `modulo` 17)($8 ~ $11)]),(UP₁₈2,[P (3 `modulo` 17)($6 ~ $7), P (14 `modulo` 17)($14 ~ $15)]),(UI₁₉3,[P (9 `modulo` 17)($7 ~ $13)]),(UI₂₀1,[P (10 `modulo` 17)($6 ~ $11)]),(UI₂₄0,[P (15 `modulo` 17)($8 ~ $15)])]}
  describe "negate" $ do
    it "should result in valid PolyL" $ do
      property $ \poly -> do
        let polynomial = PolyL.negate (poly :: PolyL (Prime 17))
        PolyL.polyConstant polynomial `shouldBe` -PolyL.polyConstant poly
        PolyL.toSlices polynomial `shouldBe` fmap (second ((-1) *)) (PolyL.toSlices poly)
        PolyL.polyRefs polynomial `shouldBe` fmap negate (PolyL.polyRefs poly)
        PolyL.validate polynomial `shouldBe` Nothing