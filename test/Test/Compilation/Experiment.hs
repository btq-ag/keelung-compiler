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
  describe "Double-width" $ do
    -- it "2 constants / Byte" $ do
    --   let program x y = return $ x `mulD` (y :: UInt 8)
    --   property $ \(x :: Word8, y :: Word8) -> do
    --     let expected = [toInteger x * toInteger y]
    --     forM_ [gf181, Prime 17, Binary 7] $ \field -> check field (program (fromIntegral x) (fromIntegral y)) [] [] expected

    -- it "2 positive variables / Byte" $ do
    --   let program = do
    --         x <- input Public :: Comp (UInt 8)
    --         y <- input Public
    --         return $ x `mulD` y

    --   property $ \(x, y :: Word8) -> do
    --     let expected = [toInteger x * toInteger y]
    --     forM_ [gf181, Prime 4099, Prime 257, Binary 7] $ \field ->
    --       check field program (map toInteger [x, y]) [] expected

    it "1 constant + 1 variable / Byte" $ do
      let program x = do
            y <- input Public :: Comp (UInt 8)
            return $ x `mulD` y
      -- debug (Binary 7) (program 129)
      property $ \(x :: Word8, y :: Word8) -> do
        let expected = [toInteger x * toInteger y]
        -- check gf181 (program (fromIntegral x)) [toInteger y] [] expected
        -- check (Prime 17) (program (fromIntegral x)) [toInteger y] [] expected
        check (Binary 7) (program (fromIntegral x)) [toInteger y] [] expected

--   let program y = do
--         x <- input Public :: Comp (UInt 8)
--         return $ x `mulD` y
--   property $ \(x, y :: Word8) -> do
--     let expected = [toInteger (x * y)]
--     forM_ [gf181, Prime 17, Binary 7] $ \field -> check field (program (fromIntegral y)) [toInteger x] [] expected

-- it "with addition / Byte" $ do
--   let program = do
--         x <- input Public :: Comp (UInt 8)
--         y <- input Public
--         z <- input Public
--         return $ x `mulD` y + z
--   property $ \(x, y, z :: Word8) -> do
--     let expected = [toInteger (x * y + z)]
--     forM_ [gf181, Prime 257, Prime 17, Binary 7] $ \field -> check field program (map toInteger [x, y, z]) [] expected

-- it "with subtraction / Byte" $ do
--   let program = do
--         x <- input Public :: Comp (UInt 8)
--         y <- input Public
--         z <- input Public
--         return $ x `mulD` y - z
--   property $ \(x, y, z :: Word8) -> do
--     let expected = [toInteger (x * y - z)]
--     forM_ [gf181, Prime 257, Prime 17, Binary 7] $ \field -> check field program (map toInteger [x, y, z]) [] expected