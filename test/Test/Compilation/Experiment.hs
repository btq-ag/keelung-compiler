{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Compilation.Experiment (run, tests) where

import Control.Monad (forM_)
import Data.Word (Word8)
import Keelung hiding (MulU, VarUI)
import Test.Arbitrary ()
import Test.Hspec
import Test.QuickCheck
import Test.Util

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Experiment" $ do
  describe "Variable-width addition" $ do
    it "2 constants / Byte -> UInt 6" $ do
      let program x y = return $ addV [x, y :: UInt 8] :: Comp (UInt 6)
      property $ \(x :: Word8, y :: Word8) -> do
        let expected = [(toInteger x + toInteger y) `mod` 64]
        check gf181 (program (fromIntegral x) (fromIntegral y)) [] [] expected

    it "2 constants / Byte -> UInt 9" $ do
      let program x y = return $ addV [x, y :: UInt 8] :: Comp (UInt 9)
      property $ \(x :: Word8, y :: Word8) -> do
        let expected = [(toInteger x + toInteger y) `mod` 512]
        check gf181 (program (fromIntegral x) (fromIntegral y)) [] [] expected

    it "2 constants / Byte -> UInt 10" $ do
      let program x y = return $ addV [x, y :: UInt 8] :: Comp (UInt 10)
      property $ \(x :: Word8, y :: Word8) -> do
        let expected = [(toInteger x + toInteger y) `mod` 1024]
        check gf181 (program (fromIntegral x) (fromIntegral y)) [] [] expected

    -- it "2 constants / Byte -> UInt 10" $ do
    --   let program x y = return $ x `mulV` (y :: UInt 8) :: Comp (UInt 10)
    --   property $ \(x :: Word8, y :: Word8) -> do
    --     let expected = [(toInteger x * toInteger y) `mod` 1024]
    --     forM_ [gf181, Prime 17, Binary 7] $ \field -> check field (program (fromIntegral x) (fromIntegral y)) [] [] expected

    -- it "2 positive variables / Byte -> UInt 6" $ do
    --   let program = do
    --         x <- input Public :: Comp (UInt 8)
    --         y <- input Public
    --         return $ x `mulV` y :: Comp (UInt 6)

    --   property $ \(x, y :: Word8) -> do
    --     let expected = [(toInteger x * toInteger y) `mod` 64]
    --     forM_ [gf181, Prime 17, Binary 7] $ \field ->
    --       check field program (map toInteger [x, y]) [] expected

    -- it "2 positive variables / Byte -> UInt 10" $ do
    --   let program = do
    --         x <- input Public :: Comp (UInt 8)
    --         y <- input Public
    --         return $ x `mulV` y :: Comp (UInt 10)

    --   property $ \(x, y :: Word8) -> do
    --     let expected = [(toInteger x * toInteger y) `mod` 1024]
    --     forM_ [gf181, Prime 17, Binary 7] $ \field ->
    --       check field program (map toInteger [x, y]) [] expected

    -- it "1 constant + 1 variable / Byte -> UInt 6" $ do
    --   let program x = do
    --         y <- input Public :: Comp (UInt 8)
    --         return $ x `mulV` y :: Comp (UInt 6)
    --   property $ \(x :: Word8, y :: Word8) -> do
    --     let expected = [(toInteger x * toInteger y) `mod` 64]
    --     check gf181 (program (fromIntegral x)) [toInteger y] [] expected
    --     check (Prime 17) (program (fromIntegral x)) [toInteger y] [] expected
    --     check (Binary 7) (program (fromIntegral x)) [toInteger y] [] expected

    -- it "1 constant + 1 variable / Byte -> UInt 10" $ do
    --   let program x = do
    --         y <- input Public :: Comp (UInt 8)
    --         return $ x `mulV` y :: Comp (UInt 10)
    --   property $ \(x :: Word8, y :: Word8) -> do
    --     let expected = [(toInteger x * toInteger y) `mod` 1024]
    --     check gf181 (program (fromIntegral x)) [toInteger y] [] expected
    --     check (Prime 17) (program (fromIntegral x)) [toInteger y] [] expected
    --     check (Binary 7) (program (fromIntegral x)) [toInteger y] [] expected