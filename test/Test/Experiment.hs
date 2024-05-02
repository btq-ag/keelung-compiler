{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Experiment (run, tests) where

import Keelung hiding (MulU, VarUI)
import Test.Hspec
import Test.QuickCheck
import Test.Util

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Experiment" $ do
  describe "DivMod" $ do
    it "variable dividend / variable divisor" $ do
      let program = do
            dividend <- input Public :: Comp (UInt 8)
            divisor <- input Public
            performDivMod dividend divisor

      let (dividend, divisor) = (10, 2)
      -- let expected = [dividend `div` divisor, dividend `mod` divisor]
      -- debug gf181 program
      -- check gf181 program [dividend, divisor] [] expected
      debugSolver gf181 program [dividend, divisor] []

    -- it "variable dividend / variable divisor" $ do
    --     let program = do
    --           dividend <- input Public :: Comp (UInt 8)
    --           divisor <- input Public
    --           performDivMod dividend divisor

    --     let genPair = do
    --           dividend <- choose (0, 255)
    --           divisor <- choose (1, 255)
    --           return (dividend, divisor)

    --     forAll genPair $ \(dividend, divisor) -> do
    --       let expected = [dividend `div` divisor, dividend `mod` divisor]
    --       check gf181 program [dividend, divisor] [] expected
    --       assertCount gf181 program 85 -- previously 163 with double allocation
    --       check (Prime 17) program [dividend, divisor] [] expected
    --       assertCount (Prime 17) program 238 -- previously 372 with double allocation
    --       check (Binary 7) program [dividend, divisor] [] expected 
    --       assertCount (Binary 7) program 771 -- previously 901 with double allocation
