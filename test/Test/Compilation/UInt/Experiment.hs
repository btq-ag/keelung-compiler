{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Experiment (tests, run) where

import Keelung hiding (compile)
import Keelung.Compiler.Options
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
    it "constant dividend / constant divisor" $ do
      let program dividend divisor = performDivMod (fromIntegral dividend) (fromIntegral divisor :: UInt 8)
      let dividend = 21
      let divisor = 64
      let expected = [dividend `div` divisor, dividend `mod` divisor]
      testCompilerWithOpts options (Binary 7) (program dividend divisor) [] [] expected
      -- debugWithOpts options (Binary 7) (program dividend divisor)

      -- let genPair = do
      --       dividend <- choose (0, 255)
      --       divisor <- choose (1, 255)
      --       return (dividend, divisor)
      -- forAll genPair $ \(dividend, divisor) -> do
      --   let expected = [dividend `div` divisor, dividend `mod` divisor]
      --   forM_ [gf181, Prime 17] $ \field -> do
      --     let options = defaultOptions {optDisableTestingOnO0 = True}
      --     testCompilerWithOpts options field (program dividend divisor) [] [] expected
      --   forM_ [Binary 7] $ \field -> do
      --     testCompiler field (program dividend divisor) [] [] expected
