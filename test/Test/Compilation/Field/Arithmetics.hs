{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Field.Arithmetics (tests, run) where

import Control.Monad
import Data.Field.Galois qualified as Galois
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "arithmetics" $ do
  describe "addition/subtraction" $ do
    describe "variables + constant" $ do
      let program constant signs = do
            inputs <- replicateM (length signs) (inputField Public)
            return $ fromIntegral constant + sum (zipWith (\sign x -> if sign then x else -x) signs inputs)

      it "GF181" $ do
        forAll arbitrary $ \(constant :: GF181, pairs :: [(Bool, GF181)]) -> do
          let (signs, values) = unzip pairs
          let expected = [toInteger (constant + sum (zipWith (\sign x -> if sign then x else -x) signs values))]
          runAll gf181 (program constant signs) (map toInteger values) [] expected

      it "Prime 2" $ do
        forAll arbitrary $ \(constant :: Galois.Prime 2, pairs :: [(Bool, Galois.Prime 2)]) -> do
          let (signs, values) = unzip pairs
          let expected = [toInteger (constant + sum (zipWith (\sign x -> if sign then x else -x) signs values))]
          runAll (Prime 2) (program constant signs) (map toInteger values) [] expected

      it "Binary 5" $ do
        forAll arbitrary $ \(constant :: Galois.Binary 5, pairs :: [(Bool, Galois.Binary 5)]) -> do
          let (signs, values) = unzip pairs
          let expected = [toInteger (constant + sum (zipWith (\sign x -> if sign then x else -x) signs values))]
          runAll (Binary 5) (program constant signs) (map toInteger values) [] expected

  describe "multiplication" $ do
    describe "variables + constant" $ do
      let program constant vars = do
            inputs <- replicateM (length vars) (inputField Public)
            return $ fromIntegral constant * product inputs

      it "GF181" $ do
        forAll arbitrary $ \(constant :: GF181, vars :: [GF181]) -> do
          let expected = [toInteger (constant * product vars)]
          runAll gf181 (program constant vars) (map toInteger vars) [] expected

      it "Prime 2" $ do
        forAll arbitrary $ \(constant :: Galois.Prime 2, vars :: [Galois.Prime 2]) -> do
          let expected = [toInteger (constant * product vars)]
          runAll (Prime 2) (program constant vars) (map toInteger vars) [] expected

      it "Binary 5" $ do
        forAll arbitrary $ \(constant :: Galois.Binary 5, vars :: [Galois.Binary 5]) -> do
          let expected = [toInteger (constant * product vars)]
          runAll (Binary 5) (program constant vars) (map toInteger vars) [] expected

  it "Mixed 1 / GF181" $ do
    let program = do
          x <- inputField Public
          y <- inputField Public
          return $ x * y + y * 2
    property $ \(x, y :: GF181) -> do
      let expected = [toInteger $ x * y + y * 2]
      runAll gf181 program [toInteger x, toInteger y] [] expected

  it "Mixed 1 / Binary 256" $ do
    let program = do
          x <- inputField Public
          y <- inputField Public
          return $ x * y + y * 2
    property $ \(x, y :: Galois.Binary 256) -> do
      let expected = [toInteger $ x * y + y * 2]
      runAll (Binary 256) program [toInteger x, toInteger y] [] expected

  it "Mixed 2 / GF181" $ do
    let program = do
          x <- inputField Public
          y <- inputField Private
          z <- reuse $ x * y + y * 2
          return $ x * y - z
    property $ \(x :: GF181, y :: GF181) -> do
      let expected = [toInteger $ -y * 2]
      runAll gf181 program [toInteger x] [toInteger y] expected

  it "Mixed 2 / Binary 256" $ do
    let program = do
          x <- inputField Public
          y <- inputField Private
          z <- reuse $ x * y + y * 2
          return $ x * y - z
    property $ \(x :: Galois.Binary 256, y :: Galois.Binary 256) -> do
      let expected = [toInteger $ -y * 2]
      runAll (Binary 256) program [toInteger x] [toInteger y] expected
