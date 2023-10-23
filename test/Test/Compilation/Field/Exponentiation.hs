{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Field.Exponentiation (tests, run) where

import Data.Field.Galois qualified as Galois
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "exponentiation" $ do
  describe "constant base" $ do
    let program base i = do
          return (base `pow` i)

    it "GF181" $ do
      let genCase = do
            power <- chooseInt (0, 100)
            base <- arbitrary
            return (base, power)

      forAll genCase $ \(base :: GF181, power) -> do
        let expected = map toInteger [base ^ power]
        runAll gf181 (program (fromIntegral base) (fromIntegral power)) [] [] expected

    it "Prime 2" $ do
      let genCase = do
            power <- chooseInt (0, 100)
            base <- arbitrary
            return (base, power)
      forAll genCase $ \(base :: Galois.Prime 2, power) -> do
        let expected = map toInteger [base ^ power]
        runAll (Prime 2) (program (fromIntegral base) (fromIntegral power)) [] [] expected

    it "Binary 7" $ do
      let genCase = do
            power <- chooseInt (0, 100)
            base <- arbitrary
            return (base, power)
      forAll genCase $ \(base :: Galois.Binary 7, power) -> do
        let expected = map toInteger [base ^ power]
        runAll (Binary 7) (program (fromIntegral base) (fromIntegral power)) [] [] expected

  describe "variable base" $ do
    let program i = do
          base <- inputField Public
          return (base `pow` i)

    it "GF181" $ do
      let genCase = do
            power <- chooseInt (0, 100)
            base <- arbitrary
            return (base, power)

      forAll genCase $ \(base :: GF181, power) -> do
        let expected = map toInteger [base ^ power]
        runAll gf181 (program (fromIntegral power)) [fromIntegral base] [] expected

    it "Prime 2" $ do
      let genCase = do
            power <- chooseInt (0, 100)
            base <- arbitrary
            return (base, power)
      forAll genCase $ \(base :: Galois.Prime 2, power) -> do
        let expected = map toInteger [base ^ power]
        runAll (Prime 2) (program (fromIntegral power)) [fromIntegral base] [] expected

    it "Binary 7" $ do
      let genCase = do
            power <- chooseInt (0, 100)
            base <- arbitrary
            return (base, power)
      forAll genCase $ \(base :: Galois.Binary 7, power) -> do
        let expected = map toInteger [base ^ power]
        runAll (Binary 7) (program (fromIntegral power)) [fromIntegral base] [] expected