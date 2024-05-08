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
  describe "divU & modU" $ do
      it "variable dividend / variable divisor" $ do
        let program = do
              dividend <- input Public :: Comp (UInt 8)
              divisor <- input Public
              return (dividend `divU` divisor, dividend `modU` divisor)

        let genPair = do
              dividend <- choose (0, 255)
              divisor <- choose (1, 255)
              return (dividend, divisor)

        forAll genPair $ \(dividend, divisor) -> do
          let expected = [dividend `div` divisor, dividend `mod` divisor]
          check gf181 program [dividend, divisor] [] expected
          assertCount gf181 program 76 -- previously 163 with double allocation
          check (Prime 17) program [dividend, divisor] [] expected
          assertCount (Prime 17) program 228 -- previously 372 with double allocation
          check (Binary 7) program [dividend, divisor] [] expected 
          assertCount (Binary 7) program 759 -- previously 901 with double allocation

      it "constant dividend / variable divisor" $ do
        let program dividend = do
              divisor <- input Public :: Comp (UInt 8)
              return (dividend `divU` divisor, dividend `modU` divisor)

        let genPair = do
              dividend <- choose (0, 255)
              divisor <- choose (1, 255)
              return (dividend, divisor)

        forAll genPair $ \(dividend, divisor) -> do
          let expected = [dividend `div` divisor, dividend `mod` divisor]
          check gf181 (program (fromIntegral dividend)) [divisor] [] expected
          check (Prime 17) (program (fromIntegral dividend)) [divisor] [] expected
          check (Binary 7) (program (fromIntegral dividend)) [divisor] [] expected

      it "variable dividend / constant divisor" $ do
        let program divisor = do
              dividend <- input Public :: Comp (UInt 8)
              return (dividend `divU` divisor, dividend `modU` divisor)
        let genPair = do
              dividend <- choose (0, 255)
              divisor <- choose (1, 255)
              return (dividend, divisor)

        forAll genPair $ \(dividend, divisor) -> do
          let expected = [dividend `div` divisor, dividend `mod` divisor]
          check gf181 (program (fromIntegral divisor)) [dividend] [] expected
          check (Prime 17) (program (fromIntegral divisor)) [dividend] [] expected
          check (Binary 7) (program (fromIntegral divisor)) [dividend] [] expected

      it "constant dividend / constant divisor" $ do
        let program dividend divisor = return (fromInteger dividend `divU` fromInteger divisor :: UInt 8, fromInteger dividend `modU` fromInteger divisor :: UInt 8)
        let genPair = do
              dividend <- choose (0, 255)
              divisor <- choose (1, 255)
              return (dividend, divisor)
        forAll genPair $ \(dividend, divisor) -> do
          let expected = [dividend `div` divisor, dividend `mod` divisor]
          check gf181 (program dividend divisor) [] [] expected
          check (Prime 17) (program dividend divisor) [] [] expected
          check (Binary 7) (program dividend divisor) [] [] expected
