{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Compilation.UInt.Logical (tests, run) where

import Control.Monad
import Data.Bits qualified
import Data.Word
import Keelung hiding (compile)
import Keelung.Data.U qualified as U
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "logical" $ do
  describe "complement" $ do
    it "constant / byte" $ do
      let program x = do
            return $ complement (x :: UInt 8)
      forAll (choose (0, 255)) $ \x -> do
        let uint = U.new 8 x
        let expected = [U.uValue (Data.Bits.complement uint)]
        forM_ [gf181, Prime 2, Binary 7] $ \field -> do
          runAll field (program (fromInteger x)) [] [] expected

    it "variable / byte" $ do
      let program = do
            x <- inputUInt @8 Public
            return $ complement x
      forAll (choose (0, 255)) $ \x -> do
        let uint = U.new 8 x
        let expected = [U.uValue (Data.Bits.complement uint)]
        forM_ [gf181, Prime 2, Binary 7] $ \field -> do
          runAll field program [U.uValue uint] [] expected

  describe "conjunction" $ do
    it "1~10 variables + constant / byte" $ do
      let program n constant = do
            xs <- replicateM n (inputUInt @8 Public)
            return $ foldl (.&.) constant xs
      forAll
        ( do
            n <- choose (1, 10)
            xs <- replicateM n arbitrary
            constant <- arbitrary
            return (n, constant, xs)
        )
        $ \(n, constant, xs :: [Word8]) -> do
          let expected = map toInteger [foldl (Data.Bits..&.) constant xs]
          forM_ [gf181, Prime 2, Binary 7] $ \field -> do
            runAll field (program n (fromIntegral constant)) (map toInteger xs) [] expected

  describe "disjunction" $ do
    it "1~10 variables + constant / byte" $ do
      let program n constant = do
            xs <- replicateM n (inputUInt @8 Public)
            return $ foldl (.|.) constant xs
      forAll
        ( do
            n <- choose (1, 10)
            xs <- replicateM n arbitrary
            constant <- arbitrary
            return (n, constant, xs)
        )
        $ \(n, constant, xs :: [Word8]) -> do
          let expected = map toInteger [foldl (Data.Bits..|.) constant xs]
          forM_ [gf181, Prime 2, Binary 7] $ \field -> do
            runAll field (program n (fromIntegral constant)) (map toInteger xs) [] expected

  describe "exclusive disjunction" $ do
    it "1~10 variables + constant / byte" $ do
      let program n constant = do
            xs <- replicateM n (inputUInt @8 Public)
            return $ foldl (.^.) constant xs
      forAll
        ( do
            n <- choose (1, 10)
            xs <- replicateM n arbitrary
            constant <- arbitrary
            return (n, constant, xs)
        )
        $ \(n, constant, xs :: [Word8]) -> do
          let expected = map toInteger [foldl Data.Bits.xor constant xs]
          forM_ [gf181, Prime 2, Binary 7] $ \field -> do
            runAll field (program n (fromIntegral constant)) (map toInteger xs) [] expected