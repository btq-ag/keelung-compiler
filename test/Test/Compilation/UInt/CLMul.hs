{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Compilation.UInt.CLMul (tests, run) where

import Data.Word
import Keelung hiding (compile)
import Keelung.Data.U qualified as U
import Test.Hspec
import Test.Compilation.Util
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "Carry-less Multiplication" $ do
    it "Constants only" $ do
      let program x y = do
            return $ x .*. (y :: UInt 6)
      let genPair = do
            x <- choose (-63, 63)
            y <- choose (-63, 63)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [U.uValue (U.clMul (U.new 6 x) (U.new 6 y))]
        runAll (Prime 5) (program (fromInteger x) (fromInteger y)) [] [] expected
        runAll (Prime 257) (program (fromInteger x) (fromInteger y)) [] [] expected

    it "2 byte variables" $ do
      let program = do
            x <- inputUInt @8 Public
            y <- inputUInt @8 Public
            return $ x .*. y
      property $ \(x :: Word8, y :: Word8) -> do
        let expected = [U.uValue (U.clMul (U.new 8 (toInteger x)) (U.new 8 (toInteger y)))]
        runAll (Prime 17) program [toInteger x, toInteger y] [] expected
        runAll (Prime 257) program [toInteger x, toInteger y] [] expected
        runAll (Prime 1031) program [toInteger x, toInteger y] [] expected

    --     it "2 Word64 variables" $ do
    --       let program = do
    --             x <- inputUInt @64 Public
    --             y <- inputUInt @64 Public
    --             return $ x .*. y
    --       property $ \(x :: Word64, y :: Word64) -> do
    --         let expected = [U.uValue (U.clMul (U.new 64 (toInteger x)) (U.new 64 (toInteger y)))]
    --         --   runAll (Prime 17) program [toInteger x, toInteger y] [] expected
    --         --   runAll (Prime 1031) program [toInteger x, toInteger y] [] expected
    --         runAll gf181 program [toInteger x, toInteger y] [] expected

    it "1 variable / 1 constant" $ do
      let program y = do
            x <- inputUInt @8 Public
            return $ x .*. fromInteger y
      let genPair = do
            x <- (arbitrary :: Gen Word8)
            y <- (arbitrary :: Gen Word8)
            return (toInteger x, toInteger y)
      forAll genPair $ \(x, y) -> do
        let expected = [U.uValue (U.clMul (U.new 8 (toInteger x)) (U.new 8 (toInteger y)))]
        runAll (Prime 17) (program y) [x] [] expected
        runAll (Prime 257) (program y) [x] [] expected
        runAll (Prime 1031) (program y) [x] [] expected

    it "2 variables / 1 constant" $ do
      let program c = do
            x <- inputUInt @8 Public
            y <- inputUInt @8 Public
            return $ x .*. y .*. fromInteger c
      let genPair = do
            x <- (arbitrary :: Gen Word8)
            y <- (arbitrary :: Gen Word8)
            c <- (arbitrary :: Gen Word8)
            return (toInteger x, toInteger y, toInteger c)
      forAll genPair $ \(x, y, c) -> do
        let expected = [U.uValue (U.new 8 (toInteger x) `U.clMul` U.new 8 (toInteger y) `U.clMul` U.new 8 (toInteger c))]
        runAll (Prime 17) (program c) [x, y] [] expected
        runAll (Prime 257) (program c) [x, y] [] expected
        runAll (Prime 1031) (program c) [x, y] [] expected

    it "3 variables / 1 constant" $ do
      let program c = do
            x <- inputUInt @8 Public
            y <- inputUInt @8 Public
            z <- inputUInt @8 Public
            return $ x .*. y .*. z .*. fromInteger c
      let genPair = do
            x <- (arbitrary :: Gen Word8)
            y <- (arbitrary :: Gen Word8)
            z <- (arbitrary :: Gen Word8)
            c <- (arbitrary :: Gen Word8)
            return (toInteger x, toInteger y, toInteger z, toInteger c)
      forAll genPair $ \(x, y, z, c) -> do
        let expected = [U.uValue (U.new 8 (toInteger x) `U.clMul` U.new 8 (toInteger y) `U.clMul` U.new 8 (toInteger z) `U.clMul` U.new 8 (toInteger c))]
        runAll (Prime 17) (program c) [x, y, z] [] expected
        runAll (Prime 257) (program c) [x, y, z] [] expected
        runAll (Prime 1031) (program c) [x, y, z] [] expected
