{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Solver.Binary (tests, run) where

import Data.Field.Galois
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Solver.Binary qualified as Binary
import Test.Hspec
import Test.QuickCheck

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

  describe "satisfiable" $ do
    it "Binary 283" $ do
      property $ \(Satisfiable polynomial assignments) -> do
        let actual = Binary.run (polynomial :: Poly (Binary 283))
        let expected = Just (assignments, [])
        actual `shouldBe` expected

-------------------------------------------------------------------------------

instance (GaloisField n, Arbitrary n) => Arbitrary (TestCase n) where
  arbitrary = do
    numberOfTerms <- choose (1, 2)
    coefficients <- vectorOf numberOfTerms (arbitrary `suchThat` (> 0)) :: Gen [n]

    assignments <- vectorOf numberOfTerms arbitrary
    let constant = sum $ zipWith (\coeff val -> if val then coeff else 0) coefficients assignments
    let polynomial = case Poly.buildEither constant (zip [0 ..] coefficients) of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly n
    pure $ Satisfiable polynomial (IntMap.fromDistinctAscList $ zip [0 ..] assignments)

data TestCase n = Satisfiable (Poly n) (IntMap Bool)
    deriving (Show)
