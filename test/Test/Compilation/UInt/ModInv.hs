{-# LANGUAGE DataKinds #-}

module Test.Compilation.UInt.ModInv (tests, run) where

import Keelung hiding (compile)
import Keelung.Interpreter.Arithmetics qualified as Arith
import Test.Compilation.Util
import Test.HUnit
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "ModInv" $ do
    it "modInv 123 (mod 2833) on Word32" $ do
      let program = return $ modInv (123 :: UInt 32) 2833
      runAll gf181 program [] [] [2119]
      runAll (Prime 17) program [] [] [2119]

    it "modInv 123 (mod 2833) on Word12" $ do
      let program = return $ modInv (123 :: UInt 12) 2833
      runAll gf181 program [] [] [2119]
      runAll (Prime 17) program [] [] [2119]

    it "modInv 3 (mod 7) on Word4" $ do
      let program = return $ modInv (3 :: UInt 4) 7
      runAll gf181 program [] [] [5]
      runAll (Prime 17) program [] [] [5]

    it "modInv N (mod 2833)" $ do
      let prime = 2833
      let program = do
            x <- input Public :: Comp (UInt 32)
            return $ modInv x prime
      let genPair = do
            -- only choosing from 1 to prime - 1
            a <- choose (1, prime - 1)
            let expected = Arith.modInv a prime
            return (a, expected)
      forAll genPair $ \(a, result) -> do
        case result of
          Nothing -> assertFailure "[ panic ] modInv: cannot find the inverse"
          Just inverse -> do
            let expected = [fromInteger inverse]
            runAll gf181 program [a] [] expected

    it "modInv 345 (mod 7919)" $ do
      let program = return $ modInv (345 :: UInt 32) 7919
      runAll gf181 program [] [] [3466]
      runAll (Prime 17) program [] [] [3466]

    it "modInv N (mod 7919)" $ do
      let prime = 7919
      let program = do
            x <- input Public :: Comp (UInt 32)
            return $ modInv x prime
      let genPair = do
            a <- choose (1, prime)
            let expected = Arith.modInv a prime
            return (a, expected)
      forAll genPair $ \(a, result) -> do
        case result of
          Nothing -> assertFailure "[ panic ] modInv: cannot find the inverse"
          Just inverse -> do
            let expected = [fromInteger inverse]
            runAll gf181 program [a] [] expected
