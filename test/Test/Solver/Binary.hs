{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Solver.Binary (tests, run) where

import Data.Field.Galois
import Data.IntMap qualified as IntMap
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Solver.Binary qualified as Binary
import Test.Hspec

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Binary" $ do
  it "$0 = 0" $ do
    let polynomial = case Poly.buildEither 0 [(0, 1)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Binary 283)
    let actual = Binary.run polynomial
    let expected = Just (IntMap.fromList [(0, False)], [])
    actual `shouldBe` expected

  it "$0 = 1" $ do
    let polynomial = case Poly.buildEither 1 [(0, 1)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Binary 283)
    let actual = Binary.run polynomial
    let expected = Just (IntMap.fromList [(0, True)], [])
    actual `shouldBe` expected

  it "$0 + 2$1 = 1" $ do
    let polynomial = case Poly.buildEither 1 [(0, 1), (1, 2)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Binary 283)
    let actual = Binary.run polynomial
    let expected = Just (IntMap.fromList [(0, True), (1, False)], [])
    actual `shouldBe` expected

  it "$0 + $1 = 1" $ do
    let polynomial = case Poly.buildEither 1 [(0, 1), (1, 1)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Binary 283)
    let actual = Binary.run polynomial
    let expected = Just (IntMap.fromList [], [polynomial])
    actual `shouldBe` expected

  it "$0 + $1 = 2" $ do
    let polynomial = case Poly.buildEither 2 [(0, 1), (1, 1)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Binary 283)
    let actual = Binary.run polynomial
    let expected = Nothing
    actual `shouldBe` expected

  it "$0 + $1 + 2$2 = 2" $ do
    let polynomial = case Poly.buildEither 2 [(0, 1), (1, 1), (2, 2)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Binary 283)
    let remaining = case Poly.buildEither 0 [(0, 1), (1, 1)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Binary 283)
    let actual = Binary.run polynomial
    let expected = Just (IntMap.fromList [(2, True)], [remaining])
    actual `shouldBe` expected