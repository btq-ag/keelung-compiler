{-# LANGUAGE DataKinds #-}

module Test.Optimization.Experiment (tests, run) where

import Keelung hiding (compileO0)
import Test.Hspec
import Test.Optimization.Util

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Experiment" $ do
  -- describe "pow" $ do
  --   let program power = do
  --         n <- input Public
  --         return (n `pow` power)
  --   describe "Frobenius endomorphism" $ do
  --     it "n^256 = n (Binary 283)" $ do
  --       (cs, cs') <- executeGF181 $ do
  --         x <- input Public
  --         y <- input Public
  --         return $ x * y
  --       cs `shouldHaveSize` 42
  --       cs' `shouldHaveSize` 33
  -- it "n^255 = n (Binary 283)" $ do
  --   property $ \(n :: Binary 283) -> do
  --     testCompiler (Binary 283) (program 255) [toInteger n] [] [1]
  -- it "n^254 = n (Binary 283)" $ do
  --   property $ \(n :: Binary 283) -> do
  --     testCompiler (Binary 283) (program 254) [toInteger n] [] [toInteger (n ^ (254 :: Int))]

  -- 8 * 3 for input / output
  -- 8 for carry bit
  -- 1 for multiplication
  it "2 variables / byte / GF181" $ do
    (cs, cs') <- executeGF181 $ do
      x <- input Public :: Comp (UInt 8)
      y <- input Public
      return $ x * y
    cs `shouldHaveSize` 42
    cs' `shouldHaveSize` 33

-- cs' `shouldHaveSize` 42
