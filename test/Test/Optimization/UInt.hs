{-# LANGUAGE DataKinds #-}

module Test.Optimization.UInt (tests, run) where

import Control.Monad (forM_)
import Keelung hiding (compileO0)
import Test.Util
import Test.Hspec
import Test.Optimization.UInt.AESMul qualified as UInt.AESMul
import Test.Optimization.UInt.CLDivMod qualified as UInt.CLDivMod
import Test.Optimization.UInt.Misc qualified as Misc
import Test.Optimization.UInt.Statement qualified as Statement

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "UInt" $ do
  UInt.CLDivMod.tests
  UInt.AESMul.tests
  Misc.tests
  Statement.tests

  describe "Variable management" $ do
    -- 4 * 3 for input / output
    -- 4 for output
    -- 1 for multiplication
    -- 8 for multiplication output - 2
    it "keelung Issue #17" $ do
      let program = do
            a <- input Private :: Comp (UInt 4)
            b <- input Private
            c <- reuse $ a * b
            return $ c .&. 5
      assertCountO0 gf181 program 28
      -- TODO: should be 23
      assertCount gf181 program 25

  describe "Addition / Subtraction" $ do
    it "2 variables / 8 bit / GF181" $ do
      -- 8 * 3 for input / output
      -- 1 for carry bit
      -- 1 for addition
      let program = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public
            return $ x + y
      assertCountO0 gf181 program 26
      assertCount gf181 program 26

    it "2 variables / 4 bit / Prime 17" $ do
      -- 12 = 4 * 3 for input / output
      -- 2 for carry bit
      -- 2 for addition
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Public
            return $ x + y
      assertCountO0 (Prime 17) program 16
      assertCount (Prime 17) program 16

    it "2 variables / 256 bit / GF181" $ do
      -- 768 = 256 * 3 for input / output
      -- 2 for carry bit
      -- 2 for addition
      let program = do
            x <- input Public :: Comp (UInt 256)
            y <- input Public
            return $ x + y
      assertCountO0 gf181 program 772
      assertCount gf181 program 772

    it "1 variable + 1 constant / byte / GF181" $ do
      -- 8 * 2 for input / output
      -- 1 for carry bit
      -- 1 for addition
      let program = do
            x <- input Public :: Comp (UInt 8)
            return $ x + 4
      assertCountO0 gf181 program 18
      assertCount gf181 program 18

    it "3 variable + 1 constant" $ do
      -- 4 * 4 for input / output
      -- 2 for carry bit
      -- 1 for addition
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Public
            z <- input Public
            return $ x + y + z + 4
      assertCountO0 gf181 program 19
      assertCount gf181 program 19

    it "3 variable + 1 constant (with subtraction)" $ do
      -- 4 * 4 for input / output
      -- 2 for carry bit
      -- 1 for addition
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Public
            z <- input Public
            return $ x - y + z + 4
      assertCountO0 gf181 program 19
      assertCount gf181 program 19

    -- TODO: should've been just 4
    -- CAUSE: constant variable need no Boolean constraints
    it "2 constants" $ do
      let program = do
            return $ 2 + (4 :: UInt 4)
      assertCountO0 gf181 program 5
      assertCount gf181 program 5

  describe "Multiplication" $ do
    -- 8 * 3 for input / output
    -- 8 for carry bit
    -- 1 for multiplication

    it "2 variables / byte / GF181" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public
            return $ x * y
      assertCountO0 gf181 program 42
      assertCount gf181 program 33

    -- 8 * 3 for input / output
    -- 4 * 5 for intermediate limbs
    -- 2 for carry bit
    -- 3 for multiplication
    -- 1 for addition

    --                      #### ####
    --         x)           #### ####
    --    -------------------------------
    --                      #### ----
    --                 #### ####
    --         +)      #### ####
    --    -------------------------------
    --                   ## #### ####
    ------------------------------------------

    it "2 variables / byte / Prime 257" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public
            return $ x * y
      assertCountO0 (Prime 257) program 55
      assertCount (Prime 257) program 50

    it "2 variables / byte / Prime 1031" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public
            return $ x * y
      assertCountO0 (Prime 1031) program 55
      assertCount (Prime 1031) program 50

    it "variable / constant" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            return $ x * 4
      assertCountO0 gf181 program 16
      assertCount gf181 program 11

    -- TODO: should've been just 4
    it "constant / constant" $ do
      let program = do
            return $ 2 * (4 :: UInt 4)
      -- print $ linkConstraintModule cs'
      assertCountO0 gf181 program 5
      assertCount gf181 program 5

  describe "Carry-less Multiplication" $ do
    -- TODO: bring this down
    it "2 byte variables" $ do
      -- constraint breakdown:
      -- I/O: 24 = 2 * 8 + 8
      -- ANDs: 36 = 8 * 9 / 2
      -- XORs: 7
      let program = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public :: Comp (UInt 8)
            return (x .*. y)
      -- print $ linkConstraintModule cs'
      assertCountO0 gf181 program 91
      assertCount gf181 program 87

  describe "Constants" $ do
    -- TODO: should be just 4
    it "`return 0`" $ do
      let program = do
            return (0 :: UInt 4)
      -- print $ linkConstraintModule cs'
      assertCountO0 gf181 program 5
      assertCount gf181 program 5

  describe "Comparison computation" $ do
    it "x ≤ y" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Private
            return $ x `lte` y
      assertCountO0 gf181 program 17
      assertCount gf181 program 16

    it "0 ≤ x" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            return $ (0 :: UInt 4) `lte` x
      assertCountO0 gf181 program 6
      assertCount gf181 program 6

    it "1 ≤ x" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            return $ (1 :: UInt 4) `lte` x
      assertCountO0 gf181 program 9
      assertCount gf181 program 8

    it "x ≤ 0" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            return $ x `lte` 0
      assertCountO0 gf181 program 8
      assertCount gf181 program 7

    it "x ≤ 1" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            return $ x `lte` 1
      assertCountO0 gf181 program 9
      assertCount gf181 program 7

    it "0 ≤ 0" $ do
      let program = do
            return $ 0 `lte` (0 :: UInt 4)
      assertCountO0 gf181 program 2
      assertCount gf181 program 2

    it "x < y" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Private
            return $ x `lt` y
      assertCountO0 gf181 program 17
      assertCount gf181 program 16

    it "x ≥ y" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Private
            return $ x `gte` y
      assertCountO0 gf181 program 17
      assertCount gf181 program 16

    it "x > y" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Private
            return $ x `gt` y
      assertCountO0 gf181 program 17
      assertCount gf181 program 16

  describe "Comparison assertion" $ do
    describe "between variables" $ do
      it "x ≤ y" $ do
        let program = do
              x <- input Public :: Comp (UInt 4)
              y <- input Private
              assert $ x `lte` y
        assertCountO0 gf181 program 16
        assertCount gf181 program 15

    it "x < y" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Private
            assert $ x `lt` y
      assertCountO0 gf181 program 16
      assertCount gf181 program 15

    it "x ≥ y" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Private
            assert $ x `gte` y
      assertCountO0 gf181 program 16
      assertCount gf181 program 15

    it "x > y" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Private
            assert $ x `gt` y
      assertCountO0 gf181 program 16
      assertCount gf181 program 15

    describe "GTE on constants (4 bits / GF181)" $ do
      let program bound = do
            x <- input Public :: Comp (UInt 4)
            assert $ x `gte` (bound :: UInt 4)
      forM_
        [ (1, 5), -- special case: the number is non-zero
          (2, 6), -- trailing zero: 1
          (3, 7),
          (4, 5), -- trailing zero: 2
          (5, 7),
          (6, 6), -- trailing zero: 1
          (7, 7),
          (8, 5), -- trailing zero: 3
          (9, 7),
          (10, 6), -- trailing zero: 1
          (11, 7),
          (12, 6), -- trailing zero: 2
          (13, 6), -- special case: only 3 possible values
          (14, 5), -- special case: only 2 possible values
          (15, 5) -- special case: only 1 possible value
        ]
        $ \(bound, expectedSize) -> do
          it ("x ≥ " <> show bound) $ do
            assertCount gf181 (program bound) expectedSize

    describe "GTE on constants (4 bits / Prime 2)" $ do
      let program bound = do
            x <- input Public :: Comp (UInt 4)
            assert $ x `gte` (bound :: UInt 4)
      forM_
        [ (1, 7), -- special case: the number is non-zero
          (2, 6), -- trailing zero: 1
          (3, 7),
          (4, 5), -- trailing zero: 2
          (5, 7),
          (6, 6), -- trailing zero: 1
          (7, 7),
          (8, 5), -- trailing zero: 3
          (9, 7),
          (10, 6), -- trailing zero: 1
          (11, 7),
          (12, 6), -- trailing zero: 2
          (13, 7), -- special case: only 3 possible values
          (14, 8), -- special case: only 2 possible values
          (15, 8) -- special case: only 1 possible value
        ]
        $ \(bound, expectedSize) -> do
          it ("x ≥ " <> show bound) $ do
            assertCount (Prime 2) (program bound) expectedSize

    describe "GTE on constants (4 bits / Prime 5)" $ do
      let program bound = do
            x <- input Public :: Comp (UInt 4)
            assert $ x `gte` (bound :: UInt 4)
      forM_
        [ (1, 5), -- special case: the number is non-zero
          (2, 6), -- trailing zero: 1
          (3, 7),
          (4, 5), -- trailing zero: 2
          (5, 7),
          (6, 6), -- trailing zero: 1
          (7, 7),
          (8, 5), -- trailing zero: 3
          (9, 7),
          (10, 6), -- trailing zero: 1
          (11, 7),
          (12, 6), -- trailing zero: 2
          (13, 8), -- special case: only 3 possible values
          (14, 7), -- special case: only 2 possible values
          (15, 6) -- special case: only 1 possible value
        ]
        $ \(bound, expectedSize) -> do
          it ("x ≥ " <> show bound) $ do
            assertCount (Prime 5) (program bound) expectedSize

    describe "LTE on constants (4 bits / GF181)" $ do
      let program bound = do
            x <- input Public :: Comp (UInt 4)
            assert $ x `lte` (bound :: UInt 4)
      forM_
        [ (0, 5), -- special case: only 1 possible value
          (1, 8), -- special case: only 2 possible value
          (2, 6), -- special case: only 3 possible value
          (3, 6), -- trailing one: 1
          (4, 7),
          (5, 6), -- trailing one: 1
          (6, 7),
          (7, 5), -- trailing one: 2
          (5, 6),
          (9, 6), -- trailing one: 1
          (10, 7),
          (11, 5), -- trailing one: 2
          (12, 7),
          (13, 6), -- trailing one: 1
          (14, 7)
        ]
        $ \(bound, expectedSize) -> do
          it ("x ≤ " <> show bound) $ do
            assertCount gf181 (program bound) expectedSize

    describe "between constants" $ do
      it "0 ≤ 0" $ do
        let program = do
              assert $ 0 `lte` (0 :: UInt 4)
        assertCountO0 gf181 program 0
        assertCount gf181 program 0
