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

  it "1 constant + 1 variable / Byte" $ do
    let program x = do
          y <- inputUInt @8 Public
          return $ x * y
    forAll arbitrary $ \(x, y :: Word8) -> do
      let expected = map toInteger [x * y]
      runAll (Binary 7) (program (fromIntegral x)) (map toInteger [y]) [] expected

  it "1 variable + 1 constant / Byte" $ do
    let program y = do
          x <- inputUInt @8 Public
          return $ x * y
    forAll arbitrary $ \(x, y :: Word8) -> do
      let expected = map toInteger [x * y]
      runAll (Binary 7) (program (fromIntegral y)) (map toInteger [x]) [] expected
