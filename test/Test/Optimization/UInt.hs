{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Optimization.UInt (tests, run) where

import Keelung hiding (compileO0)
import Test.Hspec
import Test.Optimization.Util
-- import Keelung.Compiler.Linker
-- import Keelung.Compiler.Linker (linkConstraintModule)

run :: IO ()
run = hspec tests


tests :: SpecWith ()
tests = do
  describe "UInt" $ do
    describe "Addition" $ do
        -- TODO: should've been just 15
        it "variable / variable" $ do
          (cs, cs') <- execute $ do
                x <- inputUInt @4 Public
                y <- inputUInt @4 Public
                return $ x + y
          cs `shouldHaveSize` 17
          cs' `shouldHaveSize` 17

        -- TODO: should've been just 10
        it "variable / constant" $ do
          (cs, cs') <- execute $ do
                x <- inputUInt @4 Public
                return $ x + 4
          cs `shouldHaveSize` 12
          cs' `shouldHaveSize` 12

        -- TODO: should've been just 4
        it "constant / constant" $ do
          (cs, cs') <- execute $ do
                return $ 2 + (4 :: UInt 4)
          cs `shouldHaveSize` 9
          cs' `shouldHaveSize` 9

    describe "Multiplication" $ do
        -- TODO: should've been just 13
        it "variable / variable" $ do
          (cs, cs') <- execute $ do
                x <- inputUInt @4 Public
                y <- inputUInt @4 Public
                return $ x * y
          cs `shouldHaveSize` 16
          cs' `shouldHaveSize` 16

        -- TODO: should've been just 10
        it "variable / constant" $ do
          (cs, cs') <- execute $ do
                x <- inputUInt @4 Public
                return $ x * 4
          cs `shouldHaveSize` 11
          cs' `shouldHaveSize` 11

        -- TODO: should've been just 4
        it "constant / constant" $ do
          (cs, cs') <- execute $ do
                return $ 2 * (4 :: UInt 4)
          -- print $ linkConstraintModule cs'
          cs `shouldHaveSize` 9
          cs' `shouldHaveSize` 9

    describe "Constants" $ do
      -- TODO: should be just 4
      it "`return 0`" $ do
        (cs, cs') <- execute $ do
          return (0 :: UInt 4)
        -- print $ linkConstraintModule cs'
        cs `shouldHaveSize` 9
        cs' `shouldHaveSize` 9

    describe "Comparison computation" $ do
      it "x ≤ y" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ x `lte` y
        cs `shouldHaveSize` 19
        cs' `shouldHaveSize` 18

      it "0 ≤ x" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          return $ (0 :: UInt 4) `lte` x
        cs `shouldHaveSize` 7
        cs' `shouldHaveSize` 7

      it "1 ≤ x" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          return $ (1 :: UInt 4) `lte` x
        cs `shouldHaveSize` 10
        cs' `shouldHaveSize` 9

      it "x ≤ 0" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          return $ x `lte` (0 :: UInt 4)
        cs `shouldHaveSize` 11
        cs' `shouldHaveSize` 9

      it "x ≤ 1" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          return $ x `lte` (1 :: UInt 4)
        cs `shouldHaveSize` 10
        cs' `shouldHaveSize` 8

      it "0 ≤ 0" $ do
        (cs, cs') <- execute $ do
          return $ 0 `lte` (0 :: UInt 4)
        cs `shouldHaveSize` 2
        cs' `shouldHaveSize` 2

      it "x < y" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ x `lt` y
        cs `shouldHaveSize` 19
        cs' `shouldHaveSize` 18

      it "x ≥ y" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ x `gte` y
        cs `shouldHaveSize` 19
        cs' `shouldHaveSize` 18

      it "x > y" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ x `gt` y
        cs `shouldHaveSize` 19
        cs' `shouldHaveSize` 18

    describe "Comparison assertion" $ do
      it "x ≤ y" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          assert $ x `lte` y
        cs `shouldHaveSize` 18
        cs' `shouldHaveSize` 17

      it "x ≤ 7 (LTE with trailing ones)" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          assert $ x `lte` 7
        cs `shouldHaveSize` 6
        cs' `shouldHaveSize` 6

      it "x ≥ 1 (GTE with trailing zeros)" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          -- 1000
          assert $ x `gte` 8
        cs `shouldHaveSize` 8
        cs' `shouldHaveSize` 6

      it "x ≤ 0" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          assert $ x `lte` (0 :: UInt 4)
        cs `shouldHaveSize` 9
        cs' `shouldHaveSize` 9

      it "x ≤ 1" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          assert $ x `lte` (1 :: UInt 4)
        cs `shouldHaveSize` 8
        cs' `shouldHaveSize` 8

      it "0 ≤ 0" $ do
        (cs, cs') <- execute $ do
          assert $ 0 `lte` (0 :: UInt 4)
        cs `shouldHaveSize` 0
        cs' `shouldHaveSize` 0

      it "x < y" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          assert $ x `lt` y
        cs `shouldHaveSize` 18
        cs' `shouldHaveSize` 17

      it "x ≥ y" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          assert $ x `gte` y
        cs `shouldHaveSize` 18
        cs' `shouldHaveSize` 17

      it "x > y" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          assert $ x `gt` y
        cs `shouldHaveSize` 18
        cs' `shouldHaveSize` 17

