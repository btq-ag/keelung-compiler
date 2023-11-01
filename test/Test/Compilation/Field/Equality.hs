{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Field.Equality (tests, run) where

import Data.Field.Galois qualified as Galois
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "equality" $ do
  describe "2 constants" $ do
    let program x y = do
          return $ x `eq` (y :: Field)

    it "GF181" $ do
      property $ \(x, y :: GF181) -> do
        let expected = [if x == y then 1 else 0]
        runAll gf181 (program (fromIntegral x) (fromIntegral y)) [] [] expected

    it "Prime 2" $ do
      property $ \(x, y :: Galois.Prime 2) -> do
        let expected = [if x == y then 1 else 0]
        runAll (Prime 2) (program (fromIntegral x) (fromIntegral y)) [] [] expected

    it "Binary 7" $ do
      property $ \(x, y :: Galois.Binary 7) -> do
        let expected = [if x == y then 1 else 0]
        runAll (Binary 7) (program (fromIntegral x) (fromIntegral y)) [] [] expected

  describe "variable + constant" $ do
    let program constant = do
          x <- inputField Public
          return $ x `eq` constant

    it "GF181" $ do
      property $ \(constant, value :: GF181) -> do
        let expected = [if constant == value then 1 else 0]
        runAll gf181 (program (fromIntegral constant)) [toInteger value] [] expected

    it "Prime 2" $ do
      property $ \(constant, value :: Galois.Prime 2) -> do
        let expected = [if constant == value then 1 else 0]
        runAll (Prime 2) (program (fromIntegral constant)) [toInteger value] [] expected

    it "Binary 7" $ do
      property $ \(constant, value :: Galois.Binary 7) -> do
        let expected = [if constant == value then 1 else 0]
        runAll (Binary 7) (program (fromIntegral constant)) [toInteger value] [] expected

  describe "2 variable" $ do
    let program = do
          x <- inputField Public
          y <- inputField Public
          return $ x `eq` y

    it "GF181" $ do
      property $ \(x, y :: GF181) -> do
        let expected = [if x == y then 1 else 0]
        runAll gf181 program [toInteger x, toInteger y] [] expected

    it "Prime 2" $ do
      property $ \(x, y :: Galois.Prime 2) -> do
        let expected = [if x == y then 1 else 0]
        runAll (Prime 2) program [toInteger x, toInteger y] [] expected

    it "Binary 7" $ do
      property $ \(x, y :: Galois.Binary 7) -> do
        let expected = [if x == y then 1 else 0]
        runAll (Binary 7) program [toInteger x, toInteger y] [] expected