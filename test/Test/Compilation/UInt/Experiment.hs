{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Experiment (tests, run) where

import Control.Monad
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Binary field" $ do
  -- it "2 positive variables / Byte" $ do
  --   let program = do
  --         x <- inputUInt @8 Public
  --         y <- inputUInt @8 Public
  --         return $ x * y
  --   property $ \(x, y :: Word8) -> do
  --     let expected = map toInteger [x * y]
  --     runAll (Binary 7) program (map toInteger [x, y]) [] expected

  -- it "2 positive variables / Word64" $ do
  --   let program = do
  --         x <- inputUInt @64 Public
  --         y <- inputUInt @64 Public
  --         return $ x * y
  --   property $ \(x, y :: Word64) -> do
  --     let expected = map toInteger [x * y]
  --     runAll (Binary 7) program (map toInteger [x, y]) [] expected

  it "modInv N (mod 71)" $ do
    let prime = 71
    let program = do
          x <- input Public :: Comp (UInt 8)
          return $ modInv x prime
    let expected = [22]
    forM_ [gf181, Prime 17, Binary 7] $ \field -> do
      runAll field program [42] [] expected

  it "modInv N (mod 7)" $ do
    -- 6 * 6 = 7 * 5 + 1 (mod GF181)
    let prime = 7
    let program = do
          x <- input Public :: Comp (UInt 4)
          return $ modInv x prime

    let expected = [6]
    forM_ [gf181, Prime 17, Binary 7] $ \field -> do
      runAll field program [6] [] expected
