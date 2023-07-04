{-# LANGUAGE DataKinds #-}

module Test.Solver.BinRep (tests, run) where

-- import Control.Monad
-- import Keelung hiding (compile)

import Data.Field.Galois
import Data.IntMap qualified as IntMap
import Keelung (GF181)
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Interpreter.R1CS (detectBinRep)
import Test.Hspec

-- import Test.Interpreter.Util
-- import Test.QuickCheck

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "BinRep Detection" $ do
  it "$0 + 2$1 + 4$2 = 1 (mod 11)" $ do
    let polynomial = case Poly.buildEither (-1) [(0, 1), (1, 2), (2, 4)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Prime 11)
    let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
    let expected = Just $ IntMap.fromList [(2, False), (1, False), (0, True)]
    actual `shouldBe` expected

  it "$0 + 2$1 + 4$2 = 5 (mod 11)" $ do
    let polynomial = case Poly.buildEither (-5) [(0, 1), (1, 2), (2, 4)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Prime 11)
    let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
    let expected = Just $ IntMap.fromList [(2, True), (1, False), (0, True)]
    actual `shouldBe` expected

  it "$0 - 2$1 + 4$2 = 5 (mod 11)" $ do
    let polynomial = case Poly.buildEither (-5) [(0, 1), (1, -2), (2, 4)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Prime 11)
    let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
    let expected = Just $ IntMap.fromList [(2, True), (1, False), (0, True)]
    actual `shouldBe` expected

  it "$0 - 2$1 + 4$2 = 3 (mod 11)" $ do
    let polynomial = case Poly.buildEither (-3) [(0, 1), (1, -2), (2, 4)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Prime 11)
    let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
    let expected = Just $ IntMap.fromList [(2, True), (1, True), (0, True)]
    actual `shouldBe` expected

  it "2$0 - 4$1 + 8$2 = 6 (mod 11)" $ do
    let polynomial = case Poly.buildEither (-6) [(0, 2), (1, -4), (2, 8)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Prime 11)
    let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
    let expected = Just $ IntMap.fromList [(2, True), (1, True), (0, True)]
    actual `shouldBe` expected

  it "3$0 - 6$1 + $2 = 9 (mod 11)" $ do
    let polynomial = case Poly.buildEither (-9) [(0, 3), (1, -6), (2, 1)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Prime 11)
    let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
    let expected = Just $ IntMap.fromList [(2, True), (1, True), (0, True)]
    actual `shouldBe` expected

  it "3$0 + $1 - 6$2 = 9 (mod 11)" $ do
    let polynomial = case Poly.buildEither (-9) [(0, 3), (1, 1), (2, -6)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Prime 11)
    let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
    let expected = Just $ IntMap.fromList [(1, True), (2, True), (0, True)]
    actual `shouldBe` expected

  it "9$0 + 10$1 + 7$2 = 10 (mod 11)" $ do
    let polynomial = case Poly.buildEither (-10) [(0, 9), (1, 10), (2, 7)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Prime 11)
    let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
    let expected = Just $ IntMap.fromList [(2, False), (1, True), (0, False)]
    actual `shouldBe` expected

  it "$0 - $1 = 0 (mod 11)" $ do
    let polynomial = case Poly.buildEither 0 [(0, 1), (1, -1)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Prime 11)
    let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
    let expected = Nothing
    actual `shouldBe` expected

  it "$0 - $1 = 0 (mod 17)" $ do
    let polynomial = case Poly.buildEither 0 [(0, 1), (1, -1)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Prime 17)
    let actual = IntMap.fromList <$> detectBinRep 4 (const True) polynomial
    let expected = Nothing
    actual `shouldBe` expected

  it "$0 = 1 (mod 11)" $ do
    let polynomial = case Poly.buildEither (-1) [(0, 1)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Prime 11)
    let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
    let expected = Just $ IntMap.fromList [(0, True)]
    actual `shouldBe` expected

  it "-16$17 + $24 + 2$25 + 4$26 + 8$27 - $28 - 2$29 - 4$30 - 8$31 = -7 (mod GF181)" $ do
    let polynomial = case Poly.buildEither (-7) [(17, -16), (24, 1), (25, 2), (26, 4), (27, 8), (28, -1), (29, -2), (30, -4), (31, -8)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly GF181
    let actual = IntMap.fromList <$> detectBinRep 180 (const True) polynomial
    let expected = Nothing
    actual `shouldBe` expected

  return ()