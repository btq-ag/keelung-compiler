{-# LANGUAGE DataKinds #-}

module Test.Data.LC (tests, run) where

import Data.Field.Galois ()
import Data.Field.Galois qualified as Galois
import Keelung
import Keelung.Data.FieldInfo (caseFieldType)
import Keelung.Data.LC (LC (..))
import Keelung.Data.LC qualified as LC
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.Slice qualified as Slice
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
        caseFieldType
          gf181
          ( \_ fieldInfo -> do
              LC.fromRefU fieldInfo (Right constant) `shouldBe` (expected :: [LC GF181])
          )
          undefined
      it "Prime 2" $ do
        let expected = [Constant 1, Constant 0, Constant 1, Constant 1, Constant 0, Constant 0, Constant 0, Constant 0]
        caseFieldType
          (Prime 2)
          ( \_ fieldInfo -> do
              LC.fromRefU fieldInfo (Right constant) `shouldBe` (expected :: [LC (Galois.Prime 2)])
          )
          undefined
      it "Binary 7" $ do
        let expected = [Constant 0x01, Constant 0x11, Constant 0, Constant 0]
        caseFieldType
          (Binary 7)
          undefined
          ( \_ fieldInfo -> do
              LC.fromRefU fieldInfo (Right constant) `shouldBe` (expected :: [LC (Galois.Binary 7)])
          )

    describe "converts an RefU to a list of LCs" $ do
      let intWidth = 8
      let refU = RefUX intWidth 0

      it "GF181" $ do
        let slices = Slice.fromRefUWithDesiredWidth 180 refU
        let expected = map (Polynomial . PolyL.fromSlice 0) slices
        caseFieldType
          gf181
          ( \_ fieldInfo -> do
              LC.fromRefU fieldInfo (Left refU) `shouldBe` (expected :: [LC GF181])
          )
          undefined
      it "Prime 2" $ do
        let slices = Slice.fromRefUWithDesiredWidth 1 refU
        let expected = map (Polynomial . PolyL.fromSlice 0) slices
        caseFieldType
          (Prime 2)
          ( \_ fieldInfo -> do
              LC.fromRefU fieldInfo (Left refU) `shouldBe` (expected :: [LC (Galois.Prime 2)])
          )
          undefined
      it "Binary 7" $ do
        let slices = Slice.fromRefUWithDesiredWidth 2 refU
        let expected = map (Polynomial . PolyL.fromSlice 0) slices
        caseFieldType
          (Binary 7)
          undefined
          ( \_ fieldInfo -> do
              LC.fromRefU fieldInfo (Left refU) `shouldBe` (expected :: [LC (Galois.Binary 7)])
          )