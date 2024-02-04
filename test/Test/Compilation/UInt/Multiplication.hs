{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
    let program x y = return $ x * (y :: UInt 8)
    property $ \(x, y :: Word8) -> do
      let expected = [toInteger (x * y)]
      forM_ [gf181, Prime 17, Binary 7] $ \field -> testCompiler field (program (fromIntegral x) (fromIntegral y)) [] [] expected

  it "2 positive variables / Byte" $ do
    let program = do
          x <- input Public :: Comp (UInt 8)
          y <- input Public
          return $ x * y
    property $ \(x, y :: Word8) -> do
      let expected = [toInteger (x * y)]
      forM_ [gf181, Prime 17, Binary 7] $ \field -> testCompiler field program (map toInteger [x, y]) [] expected

  it "1 constant + 1 variable / Byte" $ do
    let program x = do
          y <- input Public :: Comp (UInt 8)
          return $ x * y
    property $ \(x, y :: Word8) -> do
      let expected = [toInteger (x * y)]
      forM_ [gf181, Prime 17, Binary 7] $ \field -> testCompiler field (program (fromIntegral x)) [toInteger y] [] expected

  it "1 variable + 1 constant / Byte" $ do
    let program y = do
          x <- input Public :: Comp (UInt 8)
          return $ x * y
    property $ \(x, y :: Word8) -> do
      let expected = [toInteger (x * y)]
      forM_ [gf181, Prime 17, Binary 7] $ \field -> testCompiler field (program (fromIntegral y)) [toInteger x] [] expected

  it "with addition / Byte" $ do
    let program = do
          x <- input Public :: Comp (UInt 8)
          y <- input Public
          z <- input Public
          return $ x * y + z
    property $ \(x, y, z :: Word8) -> do
      let expected = [toInteger (x * y + z)]
      forM_ [gf181, Prime 257, Prime 17, Binary 7] $ \field -> testCompiler field program (map toInteger [x, y, z]) [] expected

  it "with subtraction / Byte" $ do
    let program = do
          x <- input Public :: Comp (UInt 8)
          y <- input Public
          z <- input Public
          return $ x * y - z
    property $ \(x, y, z :: Word8) -> do
      let expected = [toInteger (x * y - z)]
      forM_ [gf181, Prime 257, Prime 17, Binary 7] $ \field -> testCompiler field program (map toInteger [x, y, z]) [] expected

  describe "extended (double width)" $ it "2 constants / Byte" $ do
    let program x y = return $ x * (y :: UInt 8)
    property $ \(x, y :: Word8) -> do
      let expected = [toInteger (x * y)]
      forM_ [gf181, Prime 17, Binary 7] $ \field -> testCompiler field (program (fromIntegral x) (fromIntegral y)) [] [] expected