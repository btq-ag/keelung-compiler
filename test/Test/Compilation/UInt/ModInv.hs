{-# LANGUAGE DataKinds #-}

module Test.Compilation.UInt.ModInv (tests, run) where

import Control.Monad
import Keelung hiding (compile)
import Keelung.Data.U qualified as U
import Test.HUnit
import Test.Hspec
import Test.QuickCheck
import Test.Util

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "ModInv" $ do
    it "modInv 123 (mod 2833) on Word32" $ do
      let program = return $ modInv (123 :: UInt 32) 2833
      check gf181 program [] [] [2119]
      check (Prime 17) program [] [] [2119]

    it "modInv 123 (mod 2833) on Word12" $ do
      let program = return $ modInv (123 :: UInt 12) 2833
      check gf181 program [] [] [2119]
      check (Prime 17) program [] [] [2119]

    it "modInv 3 (mod 7) on Word4" $ do
      let program = return $ modInv (3 :: UInt 4) 7
      check gf181 program [] [] [5]
      check (Prime 17) program [] [] [5]

    it "modInv N (mod 2833)" $ do
      let primeNumber = 2833
      let program = do
            x <- input Public :: Comp (UInt 32)
            return $ modInv x primeNumber
      let genPair = do
            -- only choosing from 1 to primeNumber - 1
            a <- choose (1, primeNumber - 1)
            let expected = U.modInv a primeNumber
            return (a, expected)
      forAll genPair $ \(a, result) -> do
        case result of
          Nothing -> assertFailure "[ panic ] modInv: cannot find the inverse"
          Just inverse -> do
            let expected = [fromInteger inverse]
            check gf181 program [a] [] expected

    it "modInv 345 (mod 7919)" $ do
      let program = return $ modInv (345 :: UInt 32) 7919
      check gf181 program [] [] [3466]
      check (Prime 17) program [] [] [3466]

    let genPair primeNumber = do
          -- only choosing from 1 to primeNumber - 1
          a <- choose (1, primeNumber - 1)
          let expected = U.modInv a primeNumber
          return (a, expected)

    it "modInv N (mod 71)" $ do
      let primeNumber = 71
      let program = do
            x <- input Public :: Comp (UInt 8)
            return $ modInv x primeNumber
      forAll (genPair primeNumber) $ \(a, result) -> do
        case result of
          Nothing -> assertFailure "[ panic ] modInv: cannot find the inverse"
          Just inverse -> do
            let expected = [fromInteger inverse]
            forM_ [gf181, Prime 17, Binary 7] $ \field -> do
              check field program [a] [] expected

    it "modInv N (mod 7)" $ do
      let primeNumber = 7
      let program = do
            x <- input Public :: Comp (UInt 4)
            return $ modInv x primeNumber
      forAll (genPair primeNumber) $ \(a, result) -> do
        case result of
          Nothing -> assertFailure "[ panic ] modInv: cannot find the inverse"
          Just inverse -> do
            let expected = [fromInteger inverse]
            forM_ [gf181, Prime 17, Binary 7] $ \field -> do
              check field program [a] [] expected
