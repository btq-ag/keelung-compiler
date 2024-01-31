{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Optimization.UInt (tests, run) where

import Control.Monad (forM_)
import Keelung hiding (compileO0)
import Keelung.Compiler.Options
import Test.Hspec
import Test.Optimization.UInt.AESMul qualified as UInt.AESMul
import Test.Optimization.UInt.CLDivMod qualified as UInt.CLDivMod
import Test.Optimization.UInt.Misc qualified as Misc
import Test.Optimization.Util

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "UInt" $ do
  UInt.CLDivMod.tests
  UInt.AESMul.tests

  describe "Variable management" $ do
    -- can be lower
    it "keelung Issue #17 (old linker)" $ do
      (cs, cs') <- executeGF181WithOpts (defaultOptions {optUseNewLinker = False}) $ do
        a <- input Private :: Comp (UInt 5)
        b <- input Private
        c <- reuse $ a * b
        return $ c .&. 5
      cs `shouldHaveSize` 37
      cs' `shouldHaveSize` 37

    it "keelung Issue #17 (new linker, with UInt union find)" $ do
      (cs, cs') <- executeGF181WithOpts (defaultOptions {optUseNewLinker = True, optUseUIntUnionFind = True}) $ do
        a <- input Private :: Comp (UInt 5)
        b <- input Private
        c <- reuse $ a * b
        return $ c .&. 5
      cs `shouldHaveSize` 32
      -- TODO: should be 24
      cs' `shouldHaveSize` 32

    it "keelung Issue #17 (new linker, without UInt union find)" $ do
      (cs, cs') <- executeGF181WithOpts (defaultOptions {optUseNewLinker = True, optUseUIntUnionFind = False}) $ do
        a <- input Private :: Comp (UInt 5)
        b <- input Private
        c <- reuse $ a * b
        return $ c .&. 5
      cs `shouldHaveSize` 32
      -- TODO: should be 24
      cs' `shouldHaveSize` 29

  describe "Addition / Subtraction" $ do
    it "2 variables / 8 bit / GF181" $ do
      -- 8 * 3 for input / output
      -- 1 for carry bit
      -- 1 for addition
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @8 Public
        y <- inputUInt @8 Public
        return $ x + y
      cs `shouldHaveSize` 26
      cs' `shouldHaveSize` 26

    it "2 variables / 4 bit / Prime 17" $ do
      -- 12 = 4 * 3 for input / output
      -- 2 for carry bit
      -- 2 for addition
      (cs, cs') <- executePrime 17 $ do
        x <- inputUInt @4 Public
        y <- inputUInt @4 Public
        return $ x + y
      cs `shouldHaveSize` 16
      cs' `shouldHaveSize` 16

    it "2 variables / 256 bit / GF181" $ do
      -- 768 = 256 * 3 for input / output
      -- 2 for carry bit
      -- 2 for addition
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @256 Public
        y <- inputUInt @256 Public
        return $ x + y
      cs `shouldHaveSize` 772
      cs' `shouldHaveSize` 772

    it "1 variable + 1 constant / byte / GF181" $ do
      -- 8 * 2 for input / output
      -- 1 for carry bit
      -- 1 for addition
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @8 Public
        return $ x + 4
      cs `shouldHaveSize` 18
      cs' `shouldHaveSize` 18

    it "3 variable + 1 constant" $ do
      -- 4 * 4 for input / output
      -- 2 for carry bit
      -- 1 for addition
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @4 Public
        y <- inputUInt @4 Public
        z <- inputUInt @4 Public
        return $ x + y + z + 4
      cs `shouldHaveSize` 19
      cs' `shouldHaveSize` 19

    it "3 variable + 1 constant (with subtraction)" $ do
      -- 4 * 4 for input / output
      -- 2 for carry bit
      -- 1 for addition
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @4 Public
        y <- inputUInt @4 Public
        z <- inputUInt @4 Public
        return $ x - y + z + 4
      cs `shouldHaveSize` 19
      cs' `shouldHaveSize` 19

    -- TODO: should've been just 4
    -- CAUSE: constant variable need no Boolean constraints
    it "2 constants" $ do
      (cs, cs') <- executeGF181 $ do
        return $ 2 + (4 :: UInt 4)
      cs `shouldHaveSize` 5
      cs' `shouldHaveSize` 5

  describe "Multiplication" $ do
    -- 8 * 3 for input / output
    -- 8 for carry bit
    -- 1 for multiplication

    it "2 variables / byte / GF181 (old linker)" $ do
      (cs, cs') <- executeGF181WithOpts (defaultOptions {optUseNewLinker = False}) $ do
        x <- inputUInt @8 Public
        y <- inputUInt @8 Public
        return $ x * y
      cs `shouldHaveSize` 42
      cs' `shouldHaveSize` 42 -- TODO: should've been 33
      
    it "2 variables / byte / GF181 (new linker, with UInt union find)" $ do
      (cs, cs') <- executeGF181WithOpts (defaultOptions {optUseNewLinker = True, optUseUIntUnionFind = True}) $ do
        x <- inputUInt @8 Public
        y <- inputUInt @8 Public
        return $ x * y
      cs `shouldHaveSize` 42
      cs' `shouldHaveSize` 42 -- TODO: should've been 33

    it "2 variables / byte / GF181 (new linker, without UInt union find)" $ do
      (cs, cs') <- executeGF181WithOpts (defaultOptions {optUseNewLinker = True, optUseUIntUnionFind = False}) $ do
        x <- inputUInt @8 Public
        y <- inputUInt @8 Public
        return $ x * y
      cs `shouldHaveSize` 42
      cs' `shouldHaveSize` 33

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

    it "2 variables / byte / Prime 257 (old linker)" $ do
      (cs, cs') <- executePrimeWithOpts (defaultOptions {optUseNewLinker = False}) 257 $ do
        x <- inputUInt @8 Public
        y <- inputUInt @8 Public
        return $ x * y
      cs `shouldHaveSize` 55
      cs' `shouldHaveSize` 55 -- TODO: should've been 50
    it "2 variables / byte / Prime 257 (new linker, with UInt union find)" $ do
      (cs, cs') <- executePrimeWithOpts (defaultOptions {optUseNewLinker = True, optUseUIntUnionFind = True}) 257 $ do
        x <- inputUInt @8 Public
        y <- inputUInt @8 Public
        return $ x * y
      cs `shouldHaveSize` 55
      cs' `shouldHaveSize` 55 -- TODO: should've been 50
    it "2 variables / byte / Prime 257 (new linker, without UInt union find)" $ do
      (cs, cs') <- executePrimeWithOpts (defaultOptions {optUseNewLinker = True, optUseUIntUnionFind = False}) 257 $ do
        x <- inputUInt @8 Public
        y <- inputUInt @8 Public
        return $ x * y
      cs `shouldHaveSize` 55
      cs' `shouldHaveSize` 50
    
    it "2 variables / byte / Prime 1031 (old linker)" $ do
      (cs, cs') <- executePrimeWithOpts (defaultOptions {optUseNewLinker = False}) 1031 $ do
        x <- inputUInt @8 Public
        y <- inputUInt @8 Public
        return $ x * y
      cs `shouldHaveSize` 55
      cs' `shouldHaveSize` 55 -- TODO: should've been 50
    it "2 variables / byte / Prime 1031 (new linker, with UInt union find)" $ do
      (cs, cs') <- executePrimeWithOpts (defaultOptions {optUseNewLinker = True, optUseUIntUnionFind = True}) 1031 $ do
        x <- inputUInt @8 Public
        y <- inputUInt @8 Public
        return $ x * y
      cs `shouldHaveSize` 55
      cs' `shouldHaveSize` 55 -- TODO: should've been 50
    it "2 variables / byte / Prime 1031 (new linker, without UInt union find)" $ do
      (cs, cs') <- executePrimeWithOpts (defaultOptions {optUseNewLinker = True, optUseUIntUnionFind = False}) 1031 $ do
        x <- inputUInt @8 Public
        y <- inputUInt @8 Public
        return $ x * y
      cs `shouldHaveSize` 55
      cs' `shouldHaveSize` 50
    

    -- TODO: can be lower
    it "variable / constant (old linker)" $ do
      (cs, cs') <- executeGF181WithOpts (defaultOptions {optUseNewLinker = False}) $ do
        x <- inputUInt @4 Public
        return $ x * 4
      cs `shouldHaveSize` 18
      cs' `shouldHaveSize` 18 -- TODO: should've been 13
    it "variable / constant (new linker, with UInt union find)" $ do
      (cs, cs') <- executeGF181WithOpts (defaultOptions {optUseNewLinker = True, optUseUIntUnionFind = True}) $ do
        x <- inputUInt @4 Public
        return $ x * 4
      cs `shouldHaveSize` 18
      cs' `shouldHaveSize` 18 -- TODO: should've been 13
    it "variable / constant (new linker, without UInt union find)" $ do
      (cs, cs') <- executeGF181WithOpts (defaultOptions {optUseNewLinker = True, optUseUIntUnionFind = False}) $ do
        x <- inputUInt @4 Public
        return $ x * 4
      cs `shouldHaveSize` 18
      cs' `shouldHaveSize` 13

    -- TODO: should've been just 4
    it "constant / constant" $ do
      (cs, cs') <- executeGF181 $ do
        return $ 2 * (4 :: UInt 4)
      -- print $ linkConstraintModule cs'
      cs `shouldHaveSize` 5
      cs' `shouldHaveSize` 5

  describe "Carry-less Multiplication" $ do
    -- TODO: bring this down
    it "2 byte variables" $ do
      -- constraint breakdown:
      -- I/O: 24 = 2 * 8 + 8
      -- ANDs: 36 = 8 * 9 / 2
      -- XORs: 7
      (cs, cs') <- executeGF181 $ do
        x <- input Public :: Comp (UInt 8)
        y <- input Public :: Comp (UInt 8)
        return (x .*. y)
      -- print $ linkConstraintModule cs'
      cs `shouldHaveSize` 91
      cs' `shouldHaveSize` 87

  describe "Constants" $ do
    -- TODO: should be just 4
    it "`return 0`" $ do
      (cs, cs') <- executeGF181 $ do
        return (0 :: UInt 4)
      -- print $ linkConstraintModule cs'
      cs `shouldHaveSize` 5
      cs' `shouldHaveSize` 5

  -- describe "Bitwise Operators" $ do
  --   it "setBit twice" $ do
  --     (cs, cs') <- executeGF181 $ do
  --       x <- inputUInt @8 Public
  --       return $ setBit (setBit x 0 true) 1 true
  --     print cs
  --     -- print $ linkConstraintModule cs'
  --     cs `shouldHaveSize` 24
  --     cs' `shouldHaveSize` 24

  --     it "U8 -> U16" $ do
  --       (cs, cs') <- executeGF181 $ do
  --         x <- inputUInt @8 Public
  --         y <- inputUInt @8 Public
  --         return $ u8ToU16 x y
  --       print cs
  --       cs `shouldHaveSize` 528
  --       cs' `shouldHaveSize` 528
  -- where
  --   u8ToU16 :: UInt 8 -> UInt 8 -> UInt 16
  --   u8ToU16 x y =
  --     foldl (\n index -> setBit n (index + 8) (y !!! index)) (foldl (\n index -> setBit n index (x !!! index)) 0 [0 .. 7]) [0 .. 7]

  describe "Comparison computation" $ do
    it "x ≤ y" $ do
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @4 Public
        y <- inputUInt @4 Private
        return $ x `lte` y
      cs `shouldHaveSize` 17
      cs' `shouldHaveSize` 16

    it "0 ≤ x" $ do
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @4 Public
        return $ (0 :: UInt 4) `lte` x
      cs `shouldHaveSize` 6
      cs' `shouldHaveSize` 6

    it "1 ≤ x" $ do
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @4 Public
        return $ (1 :: UInt 4) `lte` x
      cs `shouldHaveSize` 9
      cs' `shouldHaveSize` 8

    it "x ≤ 0" $ do
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @4 Public
        return $ x `lte` (0 :: UInt 4)
      cs `shouldHaveSize` 8
      cs' `shouldHaveSize` 7

    it "x ≤ 1" $ do
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @4 Public
        return $ x `lte` (1 :: UInt 4)
      cs `shouldHaveSize` 9
      cs' `shouldHaveSize` 7

    it "0 ≤ 0" $ do
      (cs, cs') <- executeGF181 $ do
        return $ 0 `lte` (0 :: UInt 4)
      cs `shouldHaveSize` 2
      cs' `shouldHaveSize` 2

    it "x < y" $ do
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @4 Public
        y <- inputUInt @4 Private
        return $ x `lt` y
      cs `shouldHaveSize` 17
      cs' `shouldHaveSize` 16

    it "x ≥ y" $ do
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @4 Public
        y <- inputUInt @4 Private
        return $ x `gte` y
      cs `shouldHaveSize` 17
      cs' `shouldHaveSize` 16

    it "x > y" $ do
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @4 Public
        y <- inputUInt @4 Private
        return $ x `gt` y
      cs `shouldHaveSize` 17
      cs' `shouldHaveSize` 16

  describe "Comparison assertion" $ do
    describe "between variables" $ do
      it "x ≤ y" $ do
        (cs, cs') <- executeGF181 $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          assert $ x `lte` y
        cs `shouldHaveSize` 16
        cs' `shouldHaveSize` 15

    it "x < y" $ do
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @4 Public
        y <- inputUInt @4 Private
        assert $ x `lt` y
      cs `shouldHaveSize` 16
      cs' `shouldHaveSize` 15

    it "x ≥ y" $ do
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @4 Public
        y <- inputUInt @4 Private
        assert $ x `gte` y
      cs `shouldHaveSize` 16
      cs' `shouldHaveSize` 15

    it "x > y" $ do
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @4 Public
        y <- inputUInt @4 Private
        assert $ x `gt` y
      cs `shouldHaveSize` 16
      cs' `shouldHaveSize` 15

    describe "GTE on constants (4 bits / GF181)" $ do
      let program bound = do
            x <- inputUInt @4 Public
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
            (_, cs) <- executeGF181 (program bound)
            cs `shouldHaveSize` expectedSize

    describe "GTE on constants (4 bits / Prime 2)" $ do
      let program bound = do
            x <- inputUInt @4 Public
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
            (_, cs) <- executePrime 2 (program bound)
            cs `shouldHaveSize` expectedSize

    describe "GTE on constants (4 bits / Prime 5)" $ do
      let program bound = do
            x <- inputUInt @4 Public
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
            (_, cs) <- executePrime 5 (program bound)
            cs `shouldHaveSize` expectedSize

    describe "LTE on constants (4 bits / GF181)" $ do
      let program bound = do
            x <- inputUInt @4 Public
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
            (_, cs) <- executeGF181 (program bound)
            cs `shouldHaveSize` expectedSize

    describe "between constants" $ do
      it "0 ≤ 0" $ do
        (cs, cs') <- executeGF181 $ do
          assert $ 0 `lte` (0 :: UInt 4)
        cs `shouldHaveSize` 0
        cs' `shouldHaveSize` 0

  Misc.tests