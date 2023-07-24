{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Interpreter.UInt.Bitwise (tests, run) where

import Data.Bits qualified
import Data.Word (Word64)
import Keelung hiding (compile)
import Test.Hspec
import Test.Interpreter.Util
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Bitwise" $ do
  it "rotate left" $ do
    let program n = do
          x <- inputUInt @64 Public
          return $ x `rotate` n

    forAll arbitrary $ \(x :: Word64, n :: Int) -> do
      let expected = [toInteger (x `Data.Bits.rotateL` n)]
      runAll (Prime 2) (program n) [toInteger x] [] expected
      runAll gf181 (program n) [toInteger x] [] expected

  it "rotate right" $ do
    let program n = do
          x <- inputUInt @64 Public
          return $ x `rotate` (-n)

    forAll arbitrary $ \(x :: Word64, n :: Int) -> do
      let expected = [toInteger (x `Data.Bits.rotateR` n)]
      runAll (Prime 2) (program n) [toInteger x] [] expected
      runAll gf181 (program n) [toInteger x] [] expected

  it "shift left" $ do
    let program n = do
          x <- inputUInt @64 Public
          return $ x `shiftL` n

    forAll arbitrary $ \(x :: Word64, n :: Int) -> do
      let amount = abs n
      let expected = [toInteger (x `Data.Bits.shiftL` amount)]
      runAll (Prime 2) (program amount) [toInteger x] [] expected
      runAll gf181 (program amount) [toInteger x] [] expected

  it "shift right" $ do
    let program n = do
          x <- inputUInt @64 Public
          return $ x `shiftR` n

    forAll arbitrary $ \(x :: Word64, n :: Int) -> do
      let amount = abs n
      let expected = [toInteger (x `Data.Bits.shiftR` amount)]
      runAll (Prime 2) (program amount) [toInteger x] [] expected
      runAll gf181 (program amount) [toInteger x] [] expected