{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.CLMul (tests, run) where

import Control.Monad
import Data.Word
import Keelung hiding (compile)
import Keelung.Data.U qualified as U
import Test.Util
import Test.Hspec
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
        let expected = [toInteger (U.clMul (U.new 6 x) (U.new 6 y))]
        check (Prime 5) (program (fromInteger x) (fromInteger y)) [] [] expected
        check (Prime 257) (program (fromInteger x) (fromInteger y)) [] [] expected

    it "2 byte variables" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public
            return $ x .*. y
      property $ \(x, y :: Word8) -> do
        let expected = [toInteger (U.clMul (U.new 8 (toInteger x)) (U.new 8 (toInteger y)))]
        forM_ [gf181, Prime 17] $ \field -> do
          check field program (map toInteger [x, y]) [] expected

    it "1 variable / 1 constant" $ do
      let program y = do
            x <- input Public :: Comp (UInt 8)
            return $ x .*. fromInteger y
      property $ \(x :: Word8, y :: Word8) -> do
        let expected = [toInteger (U.clMul (U.new 8 (toInteger x)) (U.new 8 (toInteger y)))]
        forM_ [gf181, Prime 17] $ \field -> do
          check field (program (fromIntegral y)) [toInteger x] [] expected

    it "2 variables / 1 constant" $ do
      let program c = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public
            return $ x .*. y .*. fromInteger c
      property $ \(x, y :: Word8, c :: Word8) -> do
        let expected = [toInteger (U.new 8 (toInteger x) `U.clMul` U.new 8 (toInteger y) `U.clMul` U.new 8 (toInteger c))]
        forM_ [gf181, Prime 17] $ \field -> do
          check field (program (fromIntegral c)) (map toInteger [x, y]) [] expected

    it "3 variables / 1 constant" $ do
      let program c = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public
            z <- input Public
            return $ x .*. y .*. z .*. fromInteger c
      property $ \(x, y, z :: Word8, c :: Word8) -> do
        let expected = [toInteger (U.new 8 (toInteger x) `U.clMul` U.new 8 (toInteger y) `U.clMul` U.new 8 (toInteger z) `U.clMul` U.new 8 (toInteger c))]
        forM_ [gf181, Prime 17] $ \field -> do
          check field (program (fromIntegral c)) (map toInteger [x, y, z]) [] expected
