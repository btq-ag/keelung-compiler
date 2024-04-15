{-# LANGUAGE DataKinds #-}

module Test.Compilation.UInt.Addition.LimbBound (tests, run) where

import Control.Monad (replicateM)
import Data.Sequence qualified as Seq
import Keelung.Compiler.Compile.Util
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference (RefU (RefUX))
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Limb Bound Calculation" $ do
  describe "Instances" $ do
    it "0" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single True)])
      uncurry calculateBounds limbs `shouldBe` (0, 6)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [True]

    it "1" $ do
      let limbs = (3, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single True)])
      uncurry calculateBounds limbs `shouldBe` (3, 9)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [True, True]

    it "2" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single False)])
      uncurry calculateBounds limbs `shouldBe` (-3, 3)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [False]

    it "3 old" $ do
      let limbs = (1, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.MultipleOld [False, True])])
      uncurry calculateBounds limbs `shouldBe` (0, 9)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [True, True]

    it "3" $ do
      let limbs = (1, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.MultipleNew (Seq.fromList [(False, 1), (True, 1)]))])
      uncurry calculateBounds limbs `shouldBe` (0, 9)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [True, True]

    it "4 old" $ do
      let limbs = (3, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.MultipleOld [False, True])])
      uncurry calculateBounds limbs `shouldBe` (-1, 11)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [False, True]

    it "4" $ do
      let limbs = (3, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.MultipleNew (Seq.fromList [(False, 1), (True, 1)]))])
      uncurry calculateBounds limbs `shouldBe` (-1, 11)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [False, True]

    it "5 old" $ do
      let limbs = (3, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.MultipleOld [False, True])])
      uncurry calculateBounds limbs `shouldBe` (-4, 8)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [False, True]

    it "5" $ do
      let limbs = (3, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.MultipleOld [False, True])])
      uncurry calculateBounds limbs `shouldBe` (-7, 5)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [True, False]

    it "6 old" $ do
      let limbs = (3, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.MultipleOld [False, True])])
      uncurry calculateBounds limbs `shouldBe` (-7, 5)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [True, False]

    it "6" $ do
      let limbs = (3, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.MultipleNew (Seq.fromList [(False, 1), (True, 1)]))])
      uncurry calculateBounds limbs `shouldBe` (-7, 5)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [True, False]

    it "7" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.Single False)])
      uncurry calculateBounds limbs `shouldBe` (-6, 0)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [True, False]

    it "8" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single False)])
      uncurry calculateBounds limbs `shouldBe` (-3, 9)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [False, True]

    it "9" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single False)])
      uncurry calculateBounds limbs `shouldBe` (-3, 9)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [False, True]

    it "10" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.MultipleOld [False, True])])
      uncurry calculateBounds limbs `shouldBe` (-1, 11)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [False, True]

    it "11" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single True), Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.Single False)])
      uncurry calculateBounds limbs `shouldBe` (-6, 6)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [True, False]

    it "12" $ do
      let limbs = (3, Seq.fromList [Limb.new (RefUX 2 0) 1 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.Single False), Limb.new (RefUX 2 0) 2 0 (Limb.Single True)])
      uncurry calculateBounds limbs `shouldBe` (-1, 6)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [False, True]

    it "13" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 180 0) 178 0 (Limb.Single True), Limb.new (RefUX 180 0) 178 0 (Limb.Single True)])
      uncurry calculateBounds limbs `shouldBe` (0, 2 ^ (179 :: Int) - 2)
      uncurry (calculateCarrySigns 178) limbs `shouldBe` [True]

  describe "`bitSignsToRange . rangeToBitSigns`" $ do
    it "should yield wider ranges" $ do
      let genRange = do
            lower <- chooseInteger (-100, 100)
            range <- chooseInteger (0, 200)
            return (lower, lower + range)
      forAll genRange $ \(lower, upper) -> do
        let signs = rangeToBitSigns (lower, upper)
        let (lower', upper') = bitSignsToRange signs
        lower' <= lower `shouldBe` True
        upper' >= upper `shouldBe` True

  describe "`calculateSignsOfLimbs`" $ do
    it "should make non-carry bits positive" $ do
      let genLimbs = do
            width <- chooseInt (2, 8)
            let refU = RefUX width 0
            limbSize <- chooseInt (0, 8)
            signs <- replicateM limbSize arbitrary
            let limbs = map (Limb.new refU width 0 . Limb.Single) signs
            constant <- chooseInteger (0, 2 ^ width - 1)
            return (width, constant, Seq.fromList limbs)

      forAll genLimbs $ \(width, constant, limbs) -> do
        let signs = calculateSignsOfLimbs width constant limbs
        -- should be long enough
        length signs >= width `shouldBe` True
        -- should be positive
        take width signs `shouldBe` replicate width True

  describe "one special cases of `calculateCarrySigns`" $ do
    it "1 + 2bit - 2bit - 2bit - 2bit" $ do
      let limbs =
            Seq.fromList
              [ Limb.new (RefUX 2 0) 2 0 (Limb.Single True),
                Limb.new (RefUX 2 0) 2 0 (Limb.Single False),
                Limb.new (RefUX 2 0) 2 0 (Limb.Single False),
                Limb.new (RefUX 2 0) 2 0 (Limb.Single False)
              ]
      calculateCarrySigns 2 1 limbs `shouldBe` [True, False]