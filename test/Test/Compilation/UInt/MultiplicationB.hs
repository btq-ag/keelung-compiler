{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Compilation.UInt.MultiplicationB (tests, run) where

import Data.Word (Word8)
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Multiplication (Binary field)" $ do
  it "2 constants / Byte" $ do
    let program x y = do
          return $ x * (y :: UInt 8)
    forAll arbitrary $ \(x, y :: Word8) -> do
      let expected = map toInteger [x * y]
      runAll (Binary 7) (program (fromIntegral x) (fromIntegral y)) [] [] expected

  it "2 positive variables / Byte" $ do
    let program = do
          x <- inputUInt @8 Public
          y <- inputUInt @8 Public
          return $ x * y
    forAll arbitrary $ \(x, y :: Word8) -> do
      let expected = map toInteger [x * y]
      runAll (Binary 7) program (map toInteger [x, y]) [] expected

  -- it "1 positive variable + 1 negative variable / Byte" $ do
  --   let program x = do
  --         y <- inputUInt @8 Public
  --         return $ x * y
  --   forAll arbitrary $ \(x, y :: Word8) -> do
  --     let expected = map toInteger [x * y]
  --     runAll (Binary 7) (program (fromIntegral x)) (map toInteger [y]) [] expected

--   it "1 positive variable + 1 constant / Byte" $ do
--     let program y = do
--           x <- inputUInt @8 Public
--           return $ x + y
--     let genPair = do
--           x <- chooseInteger (0, 255)
--           y <- chooseInteger (0, 255)
--           return (x, y)
--     forAll genPair $ \(x, y) -> do
--       let expected = [(x + y) `mod` 256]
--       runAll (Binary 7) (program (fromInteger y)) (map toInteger [x]) [] expected

--   it "1 negative variable + 1 constant / Byte" $ do
--     let program y = do
--           x <- inputUInt @8 Public
--           return $ -x + y
--     let genPair = do
--           x <- chooseInteger (0, 255)
--           y <- chooseInteger (0, 255)
--           return (x, y)
--     forAll genPair $ \(x, y) -> do
--       let expected = [(y - x) `mod` 256]
--       runAll (Binary 7) (program (fromInteger y)) (map toInteger [x]) [] expected

--   it "1 negative variable / Byte" $ do
--     let program = do
--           x <- inputUInt @8 Public
--           return $ -x
--     forAll (chooseInteger (0, 255)) $ \x -> do
--       let expected = [(-x) `mod` 256]
--       runAll (Binary 7) program (map toInteger [x]) [] expected

--   it "mixed (positive / negative / constnat) / Byte" $ do
--     let program constant signs = do
--           inputs <- replicateM (length signs) (inputUInt @8 Public)
--           return $ constant + sum (zipWith (\sign x -> if sign then x else -x) signs inputs)
--     let genPair = do
--           n <- choose (1, 10)
--           signs <- replicateM n $ do
--             sign <- arbitrary
--             x <- chooseInteger (0, 255)
--             return (sign, x)
--           constant <- chooseInteger (0, 255)
--           return (constant, signs)
--     forAll genPair $ \(constant, pairs) -> do
--       let (signs, values) = unzip pairs
--       let expected = [(constant + sum (zipWith (\sign x -> if sign then x else -x) signs values)) `mod` 256]
--       runAll (Binary 7) (program (fromInteger constant) signs) values [] expected