{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Experiment (tests, run) where

import Keelung hiding (compile)
import Keelung.Compiler.Options
import Keelung.Data.U qualified as U
import Test.Compilation.Util
import Test.Hspec

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
  -- let options = defaultOptions {optUseUIntUnionFind = False}

  -- describe "variable / byte" $ do
  --   let program i = do
  --         x <- inputUInt Public :: Comp (UInt 8)
  --         return $ shift x i

  --   it "GF181" $ property $ \(i :: Int, x :: Word8) -> do
  --     let expected = [toInteger (Data.Bits.shift x i)]
  --     testCompilerWithOpts options gf181 (program i) [toInteger x] [] expected

  describe "DivMod" $ do
    it "performCLDivMod (dividend unknown)" $ do
      let program dividend divisor = performCLDivMod (fromInteger dividend) (fromInteger divisor :: UInt 4)
      let dividend = 0
      let divisor = 1
      let expected = [clDiv 4 dividend divisor, clMod 4 dividend divisor]
      testCompilerWithOpts options gf181 (program dividend divisor) [] [] expected

-- debugWithOpts options gf181 (program dividend divisor)
-- testCompilerWithOpts options (Prime 17) (program dividend divisor) [] [] expected

-- | Carry-less division on Integer
clDiv :: Width -> Integer -> Integer -> Integer
clDiv width x y = U.uValue (U.new width x `U.clDiv` U.new width y)

-- | Carry-less modolu on Integer
clMod :: Width -> Integer -> Integer -> Integer
clMod width x y = U.uValue (U.new width x `U.clMod` U.new width y)
