{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Experiment (tests, run) where

import Data.Field.Galois (Binary)
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Compilation Experiment" $ do
  describe "Field pow" $ do
    let program power = do
          n <- input Public
          return (n `pow` power)
    describe "Frobenius endomorphism" $ do
      it "n^256 = n (Binary 283)" $ do
        property $ \(n :: Binary 283) -> do
          runAll (Binary 283) (program 256) [toInteger n] [] [toInteger n]
      it "n^255 = n (Binary 283)" $ do
        property $ \(n :: Binary 283) -> do
          runAll (Binary 283) (program 255) [toInteger n] [] [1]
      it "n^254 = n (Binary 283)" $ do
        property $ \(n :: Binary 283) -> do
          runAll (Binary 283) (program 254) [toInteger n] [] [toInteger (n ^ (254 :: Int))]

-- debug (Binary 283) program

-- runAll gf181 (program 47) [] [] [47]
