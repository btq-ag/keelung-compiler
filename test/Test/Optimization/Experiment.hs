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
  --     validate (Binary 283) (program 255) [toInteger n] [] [1]
  -- it "n^254 = n (Binary 283)" $ do
  --   property $ \(n :: Binary 283) -> do
  --     validate (Binary 283) (program 254) [toInteger n] [] [toInteger (n ^ (254 :: Int))]

  -- 4 * 3 for input / output
  -- 4 for output
  -- 1 for multiplication
  -- 8 - 2 for multiplication output
  it "keelung Issue #17" $ do
    (cs, cs') <- executeGF181 $ do
      a <- input Private :: Comp (UInt 4)
      b <- input Private
      c <- reuse $ a * b
      return $ c .&. 5
    cs `shouldHaveSize` 28
    -- TODO: should be 23
    print cs'
    cs' `shouldHaveSize` 25
