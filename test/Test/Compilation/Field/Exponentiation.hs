{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Field.Exponentiation (tests, run) where

import Data.Field.Galois qualified as Galois
import Keelung hiding (compile)
import Test.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "exponentiation" $ do
  describe "constant base" $ do
    let genCase = do
          power <- chooseInt (0, 10)
          base <- chooseInt (0, 10)
          return (base, power)
    let program base i = do
          return (base `pow` i)

    it "GF181" $ do
      forAll genCase $ \(base, power) -> do
        let expected = map toInteger [(fromIntegral base :: GF181) ^ power]
        check gf181 (program (fromIntegral base) (fromIntegral power)) [] [] expected

    it "Prime 2" $ do
      forAll genCase $ \(base, power) -> do
        let expected = map toInteger [(fromIntegral base :: Galois.Prime 2) ^ power]
        check (Prime 2) (program (fromIntegral base) (fromIntegral power)) [] [] expected

    it "Binary 7" $ do
      forAll genCase $ \(base, power) -> do
        let expected = map toInteger [(fromIntegral base :: Galois.Binary 7) ^ power]
        check (Binary 7) (program (fromIntegral base) (fromIntegral power)) [] [] expected

  describe "variable base" $ do
    let genCase = do
          power <- chooseInt (0, 10)
          base <- chooseInt (0, 10)
          return (base, power)
    let program i = do
          base <- inputField Public
          return (base `pow` i)

    it "GF181" $ do
      forAll genCase $ \(base, power) -> do
        let expected = map toInteger [(fromIntegral base :: GF181) ^ power]
        check gf181 (program (fromIntegral power)) [fromIntegral base] [] expected

    it "Prime 2" $ do
      forAll genCase $ \(base, power) -> do
        let expected = map toInteger [(fromIntegral base :: Galois.Prime 2) ^ power]
        check (Prime 2) (program (fromIntegral power)) [fromIntegral base] [] expected

    it "Binary 7" $ do
      forAll genCase $ \(base, power) -> do
        let expected = map toInteger [(fromIntegral base :: Galois.Binary 7) ^ power]
        check (Binary 7) (program (fromIntegral power)) [fromIntegral base] [] expected