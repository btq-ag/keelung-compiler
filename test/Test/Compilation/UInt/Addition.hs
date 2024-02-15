{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Addition (tests, run) where

import Control.Monad (replicateM)
import Data.Word (Word8)
import Keelung hiding (compile)
import Test.Compilation.UInt.Addition.LimbBound qualified as LimbBound
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Addition / Subtraction" $ do
  LimbBound.tests

  describe "Prime field" $ do
    it "2 positive variables" $ do
      let program = do
            x <- input Public :: Comp (UInt 2)
            y <- input Public
            return $ x + y
      let genPair = do
            x <- chooseInteger (0, 3)
            y <- chooseInteger (0, 3)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x + y) `mod` 4]
        testCompiler (Prime 17) program [x, y] [] expected

    it "3 positive variables" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Public
            z <- input Public
            return $ x + y + z
      -- debug (Prime 17) program
      forAll (replicateM 3 (choose (0, 15))) $ \xs -> do
        let expected = [sum xs `mod` 16]
        testCompiler (Prime 17) program xs [] expected

    it "more than 4 positive variables" $ do
      let program n = do
            x <- input Public :: Comp (UInt 4)
            return $ sum (replicate (fromInteger n) x)
      forAll (choose (4, 10)) $ \n -> do
        let expected = [n * n `mod` 16]
        testCompiler (Prime 17) (program n) [n] [] expected

    it "2 positive variables / constant" $ do
      let program = do
            x <- input Public :: Comp (UInt 2)
            y <- input Public
            return $ x + y + 3
      let genPair = do
            x <- choose (0, 3)
            y <- choose (0, 3)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x + y + 3) `mod` 4]
        testCompiler (Prime 17) program [x, y] [] expected

    it "3 positive variables / constant" $ do
      let program = do
            x <- input Public :: Comp (UInt 2)
            y <- input Public
            z <- input Public
            return $ x + y + z + 3
      let genPair = do
            x <- choose (0, 3)
            y <- choose (0, 3)
            z <- choose (0, 3)
            return (x, y, z)
      forAll genPair $ \(x, y, z) -> do
        let expected = [(x + y + z + 3) `mod` 4]
        testCompiler (Prime 17) program [x, y, z] [] expected

    it "more than 4 positive variables / constant" $ do
      let program n = do
            x <- input Public :: Comp (UInt 4)
            return $ sum (replicate (fromInteger n) x) + 3
      forAll (choose (4, 10)) $ \n -> do
        let expected = [(n * n + 3) `mod` 16]
        testCompiler (Prime 17) (program n) [n] [] expected

    it "2 mixed (positive / negative) variable" $ do
      let program = do
            x <- input Public :: Comp (UInt 2)
            y <- input Public
            return $ x - y
      let genPair = do
            x <- choose (0, 3)
            y <- choose (0, 3)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x - y) `mod` 4]
        testCompiler (Prime 17) program [x, y] [] expected

    it "2 mixed (positive / negative) variable" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Public
            return $ x - y
      -- debug (Prime 17) program
      -- testCompiler (Prime 17) program [3, 13] [] [6]
      let genPair = do
            x <- choose (0, 15)
            y <- choose (0, 15)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x - y) `mod` 16]
        testCompiler (Prime 17) program [x, y] [] expected

    it "3 positive / 1 negative variables" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Public
            z <- input Public
            w <- input Public
            return $ x + y + z - w
      let genPair = do
            x <- choose (0, 15)
            y <- choose (0, 15)
            z <- choose (0, 15)
            w <- choose (0, 15)
            return (x, y, w, z)
      forAll genPair $ \(x, y, z, w) -> do
        let expected = [(x + y + z - w) `mod` 16]
        testCompiler (Prime 17) program [x, y, z, w] [] expected

    it "3 positive / 1 negative variables (negative result)" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Public
            z <- input Public
            w <- input Public
            return $ x + y + z - w

      let genPair = do
            x <- choose (0, 1)
            y <- choose (0, 1)
            z <- choose (0, 12)
            w <- choose (x, 15)
            return (x, y, w, z)
      forAll genPair $ \(x, y, z, w) -> do
        let expected = [(x + y + z - w) `mod` 16]
        testCompiler (Prime 17) program [x, y, z, w] [] expected

    -- testCompiler (Prime 17) program [0, 1, 0, 3] [] expected
    -- testCompiler (Prime 17) program [0, 1, 0, 1] [] [0]

    -- debug  (Prime 17) program
    -- testCompiler (Prime 17) program [0, 1, 0, 2] [] [15]

    -- testCompiler gf181 program [0, 1, 0, 2] [] [15]

    it "2 positive / 2 negative variables" $ do
      let program = do
            x <- input Public :: Comp (UInt 10)
            y <- input Public
            z <- input Public
            w <- input Public
            return $ x + y - z - w
      let genPair = do
            x <- choose (0, 1023)
            y <- choose (0, 1023)
            z <- choose (0, 1023)
            w <- choose (0, 1023)
            return (x, y, w, z)
      forAll genPair $ \(x, y, z, w) -> do
        let expected = [(x + y - z - w) `mod` 1024]
        -- testCompiler (Prime 5) program [x, y, z, w] [] expected
        -- testCompiler (Prime 11) program [x, y, z, w] [] expected
        testCompiler (Prime 17) program [x, y, z, w] [] expected

    it "1 positive / 3 negative variables" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Public
            z <- input Public
            w <- input Public
            return $ x - y - z - w
      let genPair = do
            x <- choose (0, 15)
            y <- choose (0, 15)
            z <- choose (0, 15)
            w <- choose (0, 15)
            return (x, y, w, z)
      forAll genPair $ \(x, y, z, w) -> do
        let expected = [(x - y - z - w) `mod` 16]
        testCompiler (Prime 17) program [x, y, z, w] [] expected

    it "4 negative variables" $ do
      let program = do
            x <- input Public :: Comp (UInt 10)
            y <- input Public
            z <- input Public
            w <- input Public
            return $ -x - y - z - w
      let genPair = do
            x <- choose (0, 1023)
            y <- choose (0, 1023)
            z <- choose (0, 1023)
            w <- choose (0, 1023)
            return (x, y, w, z)
      forAll genPair $ \(x, y, z, w) -> do
        let expected = [(-x - y - z - w) `mod` 1024]
        testCompiler (Prime 17) program [x, y, z, w] [] expected

    it "more than 2 mixed (positive / negative / constant) / UInt 4" $ do
      let program constant signs = do
            inputs <- replicateM (length signs) (input Public :: Comp (UInt 4))
            return $ constant + sum (zipWith (\sign x -> if sign then x else -x) signs inputs)
      let genPair = do
            n <- choose (2, 10)
            signs <- replicateM n $ do
              sign <- arbitrary
              x <- chooseInteger (0, 255)
              return (sign, x)
            constant <- chooseInteger (0, 255)
            return (constant, signs)
      forAll genPair $ \(constant, pairs) -> do
        let (signs, values) = unzip pairs
        let expected = [(constant + sum (zipWith (\sign x -> if sign then x else -x) signs values)) `mod` 16]
        testCompiler (Prime 17) (program (fromInteger constant) signs) values [] expected

  describe "Binary field" $ do
    it "2 positive variables / Byte" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public
            return $ x + y
      property $ \(x, y :: Word8) -> do
        let expected = [toInteger (x + y)]
        testCompiler (Binary 7) program (map toInteger [x, y]) [] expected

    it "1 positive variable + 1 negative variable / Byte" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public
            return $ x - y
      property $ \(x, y :: Word8) -> do
        let expected = [toInteger (x - y)]
        testCompiler (Binary 7) program (map toInteger [x, y]) [] expected

    it "1 positive variable + 1 constant / Byte" $ do
      let program y = do
            x <- input Public :: Comp (UInt 8)
            return $ x + y
      property $ \(x, y :: Word8) -> do
        let expected = [toInteger (x + y)]
        testCompiler (Binary 7) (program (fromIntegral y)) [toInteger x] [] expected

    it "1 negative variable + 1 constant / Byte" $ do
      let program y = do
            x <- input Public :: Comp (UInt 8)
            return $ -x + y
      property $ \(x, y :: Word8) -> do
        let expected = [toInteger (-x + y)]
        testCompiler (Binary 7) (program (fromIntegral y)) [toInteger x] [] expected

    it "1 negative variable / Byte" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            return $ -x
      property $ \(x :: Word8) -> do
        let expected = [toInteger (-x)]
        testCompiler (Binary 7) program [toInteger x] [] expected

    it "2 negative variables / UInt 2" $ do
      let program = do
            x <- input Public :: Comp (UInt 2)
            y <- input Public
            return $ -x - y
      let genPair = do
            x <- choose (0, 3)
            y <- choose (0, 3)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [toInteger (-x - y) `mod` 4]
        testCompiler (Binary 7) program [x, y] [] expected

    it "mixed (positive / negative / constnat) / Byte" $ do
      -- TODO: examine the following test case
      -- (128,[(True,0),(False,28),(False,67),(False,255),(False,33),(True,101),(True,69),(True,218),(True,229)])
      let program constant signs = do
            inputs <- replicateM (length signs) (input Public :: Comp (UInt 8))
            return $ constant + sum (zipWith (\sign x -> if sign then x else -x) signs inputs)
      let genPair = do
            n <- choose (1, 10)
            signs <- replicateM n $ do
              sign <- arbitrary
              x <- chooseInteger (0, 255)
              return (sign, x)
            constant <- chooseInteger (0, 255)
            return (constant, signs)
      forAll genPair $ \(constant, pairs) -> do
        let (signs, values) = unzip pairs
        let expected = [(constant + sum (zipWith (\sign x -> if sign then x else -x) signs values)) `mod` 256]
        testCompiler (Binary 7) (program (fromInteger constant) signs) values [] expected