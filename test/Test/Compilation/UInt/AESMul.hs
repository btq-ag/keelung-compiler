{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.AESMul (tests, run) where

-- import Data.Word

import Control.Monad
import Data.Word (Word8)
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
  describe "AES GF(256) Multiplication" $ do
    it "Constants only" $ do
      let program x y = return $ x `aesMul` (y :: UInt 8)
      property $ \(x :: Word8, y :: Word8) -> do
        let expected = [toInteger (U.aesMul (U.new 8 (toInteger x)) (U.new 8 (toInteger y)))]
        forM_ [gf181, Prime 5] $ \field -> check field (program (fromIntegral x) (fromIntegral y)) [] [] expected

    it "1 variable / 1 constant" $ do
      let program constant = do
            x <- input Public :: Comp (UInt 8)
            return $ x `aesMul` fromInteger constant
      property $ \(x :: Word8, constant :: Word8) -> do
        let expected = [toInteger (U.aesMul (U.new 8 (toInteger x)) (U.new 8 (toInteger constant)))]
        forM_ [gf181, Prime 17] $ \field -> check field (program (fromIntegral constant)) [toInteger x] [] expected

    it "2 byte variables" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public
            return $ x `aesMul` y
      property $ \(x :: Word8, y :: Word8) -> do
        let expected = [toInteger (U.aesMul (U.new 8 (toInteger x)) (U.new 8 (toInteger y)))]
        forM_ [gf181, Prime 17] $ \field -> check field program (map toInteger [x, y]) [] expected

    it "2 variables / 1 constant" $ do
      let program c = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public
            return $ x .*. y .*. fromInteger c
      property $ \(x, y :: Word8, c :: Word8) -> do
        let expected = [toInteger (U.new 8 (toInteger x) `U.clMul` U.new 8 (toInteger y) `U.clMul` U.new 8 (toInteger c))]
        forM_ [gf181, Prime 17] $ \field -> check field (program (fromIntegral c)) (map toInteger [x, y]) [] expected

    it "3 variables / 1 constant" $ do
      let program c = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public
            z <- input Public
            return $ x .*. y .*. z .*. fromInteger c
      property $ \(x, y, z :: Word8, c :: Word8) -> do
        let expected = [toInteger (U.new 8 (toInteger x) `U.clMul` U.new 8 (toInteger y) `U.clMul` U.new 8 (toInteger z) `U.clMul` U.new 8 (toInteger c))]
        forM_ [gf181, Prime 17] $ \field -> check field (program (fromIntegral c)) (map toInteger [x, y, z]) [] expected
