{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Compilation.UInt.Multiplication (tests, run) where

import Control.Monad
import Data.Word
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Multiplication" $ do
  it "2 constants / Byte" $ do
    let program x y = do
          return $ x * (y :: UInt 8)
    property $ \(x, y :: Word8) -> do
      let expected = map toInteger [x * y]
      forM_ [gf181, Prime 17, Binary 7] $ \field -> do
        runAll field (program (fromIntegral x) (fromIntegral y)) [] [] expected

  it "2 positive variables / Byte" $ do
    let program = do
          x <- inputUInt @8 Public
          y <- inputUInt @8 Public
          return $ x * y
    property $ \(x, y :: Word8) -> do
      let expected = map toInteger [x * y]
      forM_ [gf181, Prime 17, Binary 7] $ \field -> do
        runAll field program (map toInteger [x, y]) [] expected

  it "1 constant + 1 variable / Byte" $ do
    let program x = do
          y <- inputUInt @8 Public
          return $ x * y
    property $ \(x, y :: Word8) -> do
      let expected = map toInteger [x * y]
      forM_ [gf181, Prime 17, Binary 7] $ \field -> do
        runAll field (program (fromIntegral x)) (map toInteger [y]) [] expected

  it "1 variable + 1 constant / Byte" $ do
    let program y = do
          x <- inputUInt @8 Public
          return $ x * y
    property $ \(x, y :: Word8) -> do
      let expected = map toInteger [x * y]
      forM_ [gf181, Prime 17, Binary 7] $ \field -> do
        runAll field (program (fromIntegral y)) (map toInteger [x]) [] expected

  it "with addition / Byte" $ do
    let program = do
          x <- inputUInt @8 Public
          y <- inputUInt @8 Public
          z <- inputUInt @8 Public
          return $ x * y + z
    property $ \(x, y, z :: Word8) -> do
      let expected = map toInteger [x * y + z]
      forM_ [gf181, Prime 257, Prime 17, Binary 7] $ \field -> do
        runAll field program (map toInteger [x, y, z]) [] expected

  it "with subtraction / Byte" $ do
    let program = do
          x <- inputUInt @8 Public
          y <- inputUInt @8 Public
          z <- inputUInt @8 Public
          return $ x * y - z
    property $ \(x, y, z :: Word8) -> do
      let expected = map toInteger [x * y - z]
      forM_ [gf181, Prime 257, Prime 17, Binary 7] $ \field -> do
        runAll field program (map toInteger [x, y, z]) [] expected

  describe "extended (double width)" $ do
    it "2 constants / Byte" $ do
      let program x y = do
            return $ x * (y :: UInt 8)
      property $ \(x, y :: Word8) -> do
        let expected = map toInteger [x * y]
        forM_ [gf181, Prime 17, Binary 7] $ \field -> do
          runAll field (program (fromIntegral x) (fromIntegral y)) [] [] expected