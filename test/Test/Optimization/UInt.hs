{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Optimization.UInt (tests, run) where

import Control.Monad (forM_)
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
      describe "between variables" $ do
        it "x ≤ y" $ do
          (cs, cs') <- execute $ do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Private
            assert $ x `lte` y
          cs `shouldHaveSize` 18
          cs' `shouldHaveSize` 17

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

      describe "GTE on constants (4 bits)" $ do
        let program bound = do
              x <- inputUInt @4 Public
              assert $ x `gte` (bound :: UInt 4)
        forM_
          [ (1, 6), -- special case: the number is non-zero
            (2, 7), -- trailing zero: 1
            (3, 8),
            (4, 6), -- trailing zero: 2
            (5, 8),
            (6, 7), -- trailing zero: 1
            (7, 8),
            (8, 6), -- trailing zero: 3
            (9, 8),
            (10, 7), -- trailing zero: 1
            (11, 8),
            (12, 7), -- trailing zero: 2
            (13, 7), -- special case: only 3 possible values
            (14, 6), -- special case: only 2 possible values
            (15, 6) -- special case: only 1 possible value
          ]
          $ \(bound, expectedSize) -> do
            it ("x ≥ " <> show bound) $ do
              (_, cs) <- execute (program bound)
              cs `shouldHaveSize` expectedSize

      describe "LTE on constants (4 bits)" $ do
        let program bound = do
              x <- inputUInt @4 Public
              assert $ x `lte` (bound :: UInt 4)
        forM_
          [ (0, 6), -- special case: only 1 possible value
            (1, 6), -- special case: only 2 possible value
            (2, 7), -- special case: only 3 possible value
            (3, 7), -- trailing one: 1
            (4, 8),
            (5, 7), -- trailing one: 1
            (6, 8),
            (7, 6), -- trailing one: 2
            (8, 8),
            (9, 7), -- trailing one: 1
            (10, 8),
            (11, 6), -- trailing one: 2
            (12, 8),
            (13, 7), -- trailing one: 1
            (14, 8)
          ]
          $ \(bound, expectedSize) -> do
            it ("x ≥ " <> show bound) $ do
              (_, cs) <- execute (program bound)
              cs `shouldHaveSize` expectedSize

      describe "between constants" $ do
        it "0 ≤ 0" $ do
          (cs, cs') <- execute $ do
            assert $ 0 `lte` (0 :: UInt 4)
          cs `shouldHaveSize` 0
          cs' `shouldHaveSize` 0
