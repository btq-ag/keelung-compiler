{-# LANGUAGE DataKinds #-}

module Test.Data.LC (tests, run) where

import Data.Field.Galois ()
import Data.Field.Galois qualified as Galois
import Keelung
import Keelung.Data.LC
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.U qualified as U
import Test.Hspec

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "LC" $ do
  describe "fromRefU" $ do
    describe "converts an byte integer to a list of LCs" $ do
      let constant = U.new 8 13
      it "GF181" $ do
        let expected = [Constant 13]
        fromRefU 180 (Right constant) `shouldBe` (expected :: [LC GF181])
      it "Prime 2" $ do
        let expected = [Constant 1, Constant 0, Constant 1, Constant 1, Constant 0, Constant 0, Constant 0, Constant 0]
        fromRefU 1 (Right constant) `shouldBe` (expected :: [LC (Galois.Prime 2)])
      it "Binary 7" $ do
        let expected = [Constant 0x01, Constant 0x11, Constant 0, Constant 0]
        fromRefU 2 (Right constant) `shouldBe` (expected :: [LC (Galois.Binary 7)])

    describe "converts an RefU to a list of LCs" $ do
      let intWidth = 8
      let refU = RefUX intWidth 0

      it "GF181" $ do
        let limbs = Limb.refUToLimbs 180 refU
        let expected = map (Polynomial . PolyL.fromLimb 0) limbs
        fromRefU 180 (Left refU) `shouldBe` (expected :: [LC GF181])
      it "Prime 2" $ do
        let limbs = Limb.refUToLimbs 1 refU
        let expected = map (Polynomial . PolyL.fromLimb 0) limbs
        fromRefU 1 (Left refU) `shouldBe` (expected :: [LC (Galois.Prime 2)])
      it "Binary 7" $ do
        let limbs = Limb.refUToLimbs 2 refU
        let expected = map (Polynomial . PolyL.fromLimb 0) limbs
        fromRefU 2 (Left refU) `shouldBe` (expected :: [LC (Galois.Binary 7)])