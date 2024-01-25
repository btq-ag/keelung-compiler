{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Experiment (tests, run) where

import Data.Binary
import Data.Bits qualified
import Keelung hiding (compile)
import Keelung.Compiler.Options
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Compilation Experiment" $ do
  -- describe "Field pow" $ do
  --   let program power = do
  --         n <- input Public
  --         return (n `pow` power)
  --   describe "Frobenius endomorphism" $ do
  --     it "n^256 = n (Binary 283)" $ do
  --       property $ \(n :: Binary 283) -> do
  --         testCompilerWithOpts options (Binary 283) (program 256) [toInteger n] [] [toInteger n]
  --     it "n^255 = n (Binary 283)" $ do
  --       property $ \(n :: Binary 283) -> do
  --         testCompilerWithOpts options (Binary 283) (program 255) [toInteger n] [] [1]
  --     it "n^254 = n (Binary 283)" $ do
  --       property $ \(n :: Binary 283) -> do
  --         testCompilerWithOpts options (Binary 283) (program 254) [toInteger n] [] [toInteger (n ^ (254 :: Int))]

  let options = defaultOptions {optUseUIntUnionFind = True}

  describe "variable / byte" $ do
    let program i = do
          x <- inputUInt Public :: Comp (UInt 8)
          return $ shift x i

    it "GF181" $ property $ \(i :: Int, x :: Word8) -> do
      let expected = [toInteger (Data.Bits.shift x i)]
      testCompilerWithOpts options gf181 (program i) [toInteger x] [] expected
