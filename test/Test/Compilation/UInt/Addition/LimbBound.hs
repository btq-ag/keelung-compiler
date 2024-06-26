{-# LANGUAGE DataKinds #-}

module Test.Compilation.UInt.Addition.LimbBound (tests, run) where

import Control.Monad (replicateM)
import Data.Sequence qualified as Seq
import Keelung.Compiler.Compile.Util
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference (RefU (RefUX))
import Keelung.Data.Slice (Slice (Slice))
import Test.Hspec
import Test.QuickCheck
import Keelung (widthOf)

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Limb Bound Calculation" $ do
  describe "Instances" $ do
    it "0" $ do
      let limbs = (0, Seq.fromList [Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) True])
      uncurry calculateBounds limbs `shouldBe` (0, 6)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` Seq.fromList [(True, 1)]

    it "1" $ do
      let limbs = (3, Seq.fromList [Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) True])
      uncurry calculateBounds limbs `shouldBe` (3, 9)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` Seq.fromList [(True, 2)]

    it "2" $ do
      let limbs = (0, Seq.fromList [Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) False])
      uncurry calculateBounds limbs `shouldBe` (-3, 3)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` Seq.fromList [(False, 1)]

    it "3" $ do
      let limbs = (1, Seq.fromList [Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.CarryLimb (RefUX 2 0) (Seq.fromList [(False, 1), (True, 1)])])
      uncurry calculateBounds limbs `shouldBe` (0, 9)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` Seq.fromList [(True, 2)]

    it "4" $ do
      let limbs = (3, Seq.fromList [Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) False, Limb.CarryLimb (RefUX 2 0) (Seq.fromList [(False, 1), (True, 1)])])
      uncurry calculateBounds limbs `shouldBe` (-1, 11)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` Seq.fromList [(False, 1), (True, 1)]

    it "5" $ do
      let limbs = (3, Seq.fromList [Limb.newOperand (Slice (RefUX 2 0) 0 2) False, Limb.newOperand (Slice (RefUX 2 0) 0 2) False, Limb.newOperand (Slice (RefUX 2 0) 0 2) False, Limb.CarryLimb (RefUX 2 0) (Seq.fromList [(False, 1), (True, 1)])])
      uncurry calculateBounds limbs `shouldBe` (-7, 5)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` Seq.fromList [(True, 1), (False, 1)]

    it "6" $ do
      let limbs = (3, Seq.fromList [Limb.newOperand (Slice (RefUX 2 0) 0 2) False, Limb.newOperand (Slice (RefUX 2 0) 0 2) False, Limb.newOperand (Slice (RefUX 2 0) 0 2) False, Limb.CarryLimb (RefUX 2 0) (Seq.fromList [(False, 1), (True, 1)])])
      uncurry calculateBounds limbs `shouldBe` (-7, 5)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` Seq.fromList [(True, 1), (False, 1)]

    it "7" $ do
      let limbs = (0, Seq.fromList [Limb.newOperand (Slice (RefUX 2 0) 0 2) False, Limb.newOperand (Slice (RefUX 2 0) 0 2) False])
      uncurry calculateBounds limbs `shouldBe` (-6, 0)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` Seq.fromList [(True, 1), (False, 1)]

    it "8" $ do
      let limbs = (0, Seq.fromList [Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) False])
      uncurry calculateBounds limbs `shouldBe` (-3, 9)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` Seq.fromList [(False, 1), (True, 1)]

    it "9" $ do
      let limbs = (0, Seq.fromList [Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) False])
      uncurry calculateBounds limbs `shouldBe` (-3, 9)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` Seq.fromList [(False, 1), (True, 1)]

    it "10" $ do
      let limbs = (0, Seq.fromList [Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.CarryLimb (RefUX 2 0) (Seq.fromList [(False, 1), (True, 1)])])
      uncurry calculateBounds limbs `shouldBe` (-1, 11)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` Seq.fromList [(False, 1), (True, 1)]

    it "11" $ do
      let limbs = (0, Seq.fromList [Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) True, Limb.newOperand (Slice (RefUX 2 0) 0 2) False, Limb.newOperand (Slice (RefUX 2 0) 0 2) False])
      uncurry calculateBounds limbs `shouldBe` (-6, 6)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` Seq.fromList [(True, 1), (False, 1)]

    it "12" $ do
      let limbs = (3, Seq.fromList [Limb.newOperand (Slice (RefUX 2 0) 0 2) False, Limb.newOperand (Slice (RefUX 2 0) 0 2) False, Limb.newOperand (Slice (RefUX 2 0) 0 2) True])
      uncurry calculateBounds limbs `shouldBe` (-3, 6)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` Seq.fromList [(False, 1), (True, 1)]

    it "13" $ do
      let limbs = (0, Seq.fromList [Limb.newOperand (Slice (RefUX 180 0) 0 178) True, Limb.newOperand (Slice (RefUX 180 0) 0 178) True])
      uncurry calculateBounds limbs `shouldBe` (0, 2 ^ (179 :: Int) - 2)
      uncurry (calculateCarrySigns 178) limbs `shouldBe` Seq.fromList [(True, 1)]

  describe "`bitSignsToRange . rangeToBitSigns`" $ it "should yield wider ranges" $ do
    let genRange = do
          lower <- chooseInteger (-100, 100)
          range <- chooseInteger (0, 200)
          return (lower, lower + range)
    forAll genRange $ \(lower, upper) -> do
      let signs = rangeToBitSigns (lower, upper)
      let (lower', upper') = bitSignsToRange signs
      lower' <= lower `shouldBe` True
      upper' >= upper `shouldBe` True

  describe "`calculateSignsOfLimbs`" $ it "should make non-carry bits positive" $ do
    let genLimbs = do
          width <- chooseInt (2, 8)
          let refU = RefUX width 0
          limbSize <- chooseInt (0, 8)
          signs <- replicateM limbSize arbitrary
          let limbs = map (Limb.newOperand (Slice refU 0 width)) signs
          constant <- chooseInteger (0, 2 ^ width - 1)
          return (width, constant, Seq.fromList limbs)

    forAll genLimbs $ \(width, constant, limbs) -> do
      let signs = calculateSignsOfLimbs width constant limbs
      -- should be long enough
      widthOf signs >= width `shouldBe` True
      -- should be positive
      fst (Limb.splitAtSigns width signs) `shouldBe` Seq.fromList [(True, width)]

  describe "one special cases of `calculateCarrySigns`" $ it "1 + 2bit - 2bit - 2bit - 2bit" $ do
    let limbs =
          Seq.fromList
            [ Limb.newOperand (Slice (RefUX 2 0) 0 2) True,
              Limb.newOperand (Slice (RefUX 2 0) 0 2) False,
              Limb.newOperand (Slice (RefUX 2 0) 0 2) False,
              Limb.newOperand (Slice (RefUX 2 0) 0 2) False
            ]
    calculateCarrySigns 2 1 limbs `shouldBe` Seq.fromList [(True, 1), (False, 1)]