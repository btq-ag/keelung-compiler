{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Test.Optimization (tests, run) where

import Data.Foldable
import Hash.Poseidon qualified as Poseidon
import Keelung hiding (compileO0)
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.Relations qualified as Relations
import Keelung.Data.Reference
import Test.Util
import Test.Hspec
import Test.Optimization.UInt qualified as Optimization.UInt

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "Constraint minimization" $ do
    Optimization.UInt.tests

    it "Poseidon" $ do
      let program = do
            xs <- inputList Public 1
            Poseidon.hash (toList xs)

      -- cm before `pow`: 1537
      assertCountO0 gf181 program 555
      -- cm' before `pow`: 694
      assertCount gf181 program 552

      return ()

    describe "Field" $ do
      it "Field 1" $ do
        let program = do
              x <- inputField Public
              y <- reuse x
              z <- reuse x
              return (x + y + z)

        assertCountO0 gf181 program 3
        assertCount gf181 program 1

        cm <- compileAsConstraintModule gf181 program :: IO (ConstraintModule GF181)

        -- FO0 = 3FI0
        Relations.relationBetween (F $ RefFO 0) (F $ RefFI 0) (cmRelations cm) `shouldBe` Just (3, 0)
        -- F0 (y) = FI0
        Relations.relationBetween (F $ RefFX 0) (F $ RefFI 0) (cmRelations cm) `shouldBe` Just (1, 0)
        -- F1 (z) = F0 (y)
        Relations.relationBetween (F $ RefFX 1) (F $ RefFX 0) (cmRelations cm) `shouldBe` Just (1, 0)

      it "Field 2" $ do
        let program = do
              x <- inputField Public
              y <- reuse x
              z <- reuse (x + y)
              return (x + y + z)

        assertCountO0 gf181 program 3
        assertCount gf181 program 1

        cm <- compileAsConstraintModule gf181 program :: IO (ConstraintModule GF181)
        -- FO0 = 4FI0
        Relations.relationBetween (F $ RefFO 0) (F $ RefFI 0) (cmRelations cm) `shouldBe` Just (4, 0)
        -- F0 (y) = FI0
        Relations.relationBetween (F $ RefFX 0) (F $ RefFI 0) (cmRelations cm) `shouldBe` Just (1, 0)
        -- F1 (z) = 2F0 (y)
        Relations.relationBetween (F $ RefFX 1) (F $ RefFX 0) (cmRelations cm) `shouldBe` Just (2, 0)

      it "Field 3" $ do
        let program = do
              x <- inputField Public
              y <- reuse (x + 1)
              return (x + y)

        assertCountO0 gf181 program 2
        assertCount gf181 program 1

        cm <- compileAsConstraintModule gf181 program :: IO (ConstraintModule GF181)
        -- FO0 = 2FI0 + 1
        Relations.relationBetween (F $ RefFO 0) (F $ RefFI 0) (cmRelations cm) `shouldBe` Just (2, 1)

      it "Field 4" $ do
        let program = do
              let x = 4
              y <- reuse x
              return (x + y :: Field)

        assertCountO0 gf181 program 1
        assertCount gf181 program 1
        cm <- compileAsConstraintModule gf181 program :: IO (ConstraintModule GF181)
        Relations.lookupRef (F $ RefFO 0) (cmRelations cm) `shouldBe` Relations.Constant 8

      it "Field 5" $ do
        let program = do
              x <- inputField Public
              y <- reuse x
              return (x * y :: Field)
        assertCountO0 gf181 program 3
        assertCount gf181 program 1

    describe "Boolean" $ do
      it "Boolean 1" $ do
        let program = do
              x <- inputBool Public
              y <- reuse x
              return (x .|. y)
        assertCountO0 gf181 program 5
        assertCount gf181 program 3

      it "Boolean 2" $ do
        let program = do
              x <- inputBool Public
              reuse x

        assertCountO0 gf181 program 3
        assertCount gf181 program 3