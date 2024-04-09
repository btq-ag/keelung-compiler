{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Field.Inequality (tests, run) where

import Data.Field.Galois qualified as Galois
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "inequality" $ do
  describe "2 constants" $ do
    let program x y = do
          return $ x `neq` (y :: Field)

    it "GF181" $ do
      property $ \(x, y :: GF181) -> do
        let expected = [if x == y then 0 else 1]
        validate gf181 (program (fromIntegral x) (fromIntegral y)) [] [] expected

    it "Prime 2" $ do
      property $ \(x, y :: Galois.Prime 2) -> do
        let expected = [if x == y then 0 else 1]
        validate (Prime 2) (program (fromIntegral x) (fromIntegral y)) [] [] expected

    it "Binary 7" $ do
      property $ \(x, y :: Galois.Binary 7) -> do
        let expected = [if x == y then 0 else 1]
        validate (Binary 7) (program (fromIntegral x) (fromIntegral y)) [] [] expected

  describe "variable + constant" $ do
    let program constant = do
          x <- inputField Public
          return $ x `neq` constant

    it "GF181" $ do
      property $ \(constant, value :: GF181) -> do
        let expected = [if constant == value then 0 else 1]
        validate gf181 (program (fromIntegral constant)) [toInteger value] [] expected

    it "Prime 2" $ do
      property $ \(constant, value :: Galois.Prime 2) -> do
        let expected = [if constant == value then 0 else 1]
        validate (Prime 2) (program (fromIntegral constant)) [toInteger value] [] expected

    it "Binary 7" $ do
      property $ \(constant, value :: Galois.Binary 7) -> do
        let expected = [if constant == value then 0 else 1]
        validate (Binary 7) (program (fromIntegral constant)) [toInteger value] [] expected

  describe "2 variable" $ do
    let program = do
          x <- inputField Public
          y <- inputField Public
          return $ x `neq` y

    it "GF181" $ do
      property $ \(x, y :: GF181) -> do
        let expected = [if x == y then 0 else 1]
        validate gf181 program [toInteger x, toInteger y] [] expected

    it "Prime 2" $ do
      property $ \(x, y :: Galois.Prime 2) -> do
        let expected = [if x == y then 0 else 1]
        validate (Prime 2) program [toInteger x, toInteger y] [] expected

    it "Binary 7" $ do
      property $ \(x, y :: Galois.Binary 7) -> do
        let expected = [if x == y then 0 else 1]
        validate (Binary 7) program [toInteger x, toInteger y] [] expected