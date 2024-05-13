{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Solver.BinRep (tests, run) where

import Data.Field.Galois (GaloisField, Prime, Binary)
import Data.IntMap qualified as IntMap
import Data.IntMap.Strict (IntMap)
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Field (GF181)
import Keelung.Solver (BinRep (..), assignBinRep, detectBinRep, rangeOfBinRep)
import Test.Hspec
import Test.QuickCheck
import Keelung.Compiler.Util (powerOf2)

-- import Test.QuickCheck

run :: IO ()
run = hspec tests

-- | Test cases for BinRep detection
data TestDetection
  = -- | construct a BinRep that can be successfully detected
    DetectionSuccess
  | -- | two coefficients have the same power
    DetectionDuplicatedCoefficients
  | -- | more than `fieldBitWidth` number of coefficients
    DetectionTooManyCoefficients
  deriving (Show, Eq)

-- | Test cases for BinRep assignment
data TestAssignment
  = -- | construct a satisfiable BinRep
    AssignmentSatisfiable
  | -- | construct a unsatisfiable BinRep
    AssignmentConstantOutOfRange
  deriving (Show, Eq)

instance Arbitrary TestDetection where
  arbitrary = elements [DetectionSuccess, DetectionDuplicatedCoefficients, DetectionTooManyCoefficients]

instance Arbitrary TestAssignment where
  arbitrary = return AssignmentSatisfiable

-- | Given the number of desired coefficients, generate a BinRep
genBinRep :: (GaloisField n, Integral n) => Int -> Gen (BinRep n)
genBinRep n = do
  -- generate excess coefficients (so that we can remove some of them later)
  signs <- vectorOf (n * 2) arbitrary -- Bool
  vars <- shuffle [0 .. n * 2 - 1] -- Var

  -- zip all of them together, and shuffle them
  -- take only `n` number of coefficients
  tuples <- take n <$> shuffle (zip signs vars)
  let zipped = zip [0 ..] tuples -- zip with powers
  let coeffs = IntMap.fromList zipped
  let (lowerBound, upperBound) = rangeOfBinRep coeffs
  return $ BinRep coeffs lowerBound upperBound

-- | Given a BinRep, generate some assignments and a valid polynomial
genPoly :: (GaloisField n, Integral n) => BinRep n -> Gen (Poly n, (IntMap Bool, (n, n)))
genPoly binPolys = do
  xs <- shuffle $ IntMap.toList $ binPolyCoeffs binPolys
  multiplier <- suchThat arbitrary (> 0)
  values <- vectorOf (length xs) arbitrary
  let (coeffs, lowerBound, constant, upperBound) =
        foldl
          ( \(poly, l, c, u) ((power, (sign, var)), assignment) ->
              let coeff = multiplier * powerOf2 power
               in if sign
                    then ((var, coeff) : poly, l, c + (if assignment then 1 else 0) * coeff, u + coeff)
                    else ((var, -coeff) : poly, l - coeff, c - (if assignment then 1 else 0) * coeff, u)
          )
          -- go :: (GaloisField n, Integral n) => (n, n) -> Int -> (Bool, Var) -> (n, n)
          -- go (lowerBound, upperBound) power (True, _) = (lowerBound, upperBound + powerOf2 power)
          -- go (lowerBound, upperBound) power (False, _) = (lowerBound - powerOf2 power, upperBound)

          ([], 0, 0, 0)
          (zip xs values)
  let assignments = IntMap.fromList $ zipWith (\(_power, (_sign, var)) val -> (var, val)) xs values

  case Poly.buildEither (-constant) coeffs of
    Left _ -> error "Poly.buildEither"
    Right poly -> return (poly, (assignments, (lowerBound, upperBound)))

genTestDetection :: (Integral n, GaloisField n) => Int -> Gen (Poly n, Maybe (BinRep n))
genTestDetection fieldBitWidth = do
  -- decide if we want this BinRep to be detected or not
  scenario <- arbitrary
  case scenario of
    DetectionSuccess -> do
      size <- choose (1, fieldBitWidth)
      binPoly <- genBinRep size
      polynomial <- fst <$> genPoly binPoly
      return (polynomial, Just binPoly)
    DetectionDuplicatedCoefficients -> do
      size <- choose (2, fieldBitWidth)
      binPoly <- genBinRep size
      polynomial <- fst <$> genPoly binPoly
      -- tweak the polynomial so that it has duplicated coefficients
      let coeffs = case IntMap.toList (Poly.coeffs polynomial) of
            (power1, coeff1) : (power2, _coeff2) : rest -> (power1, coeff1) : (power2, coeff1) : rest
            _ -> error "[ panic ] genTestDetection.DuplicatedCoefficients impossible"
      let polynomial' = case Poly.buildEither (Poly.constant polynomial) coeffs of
            Left _ -> error "Poly.buildEither"
            Right p -> p
      return (polynomial', Nothing)
    DetectionTooManyCoefficients -> do
      size <- choose (fieldBitWidth + 1, fieldBitWidth + 2)
      binPoly <- genBinRep size
      polynomial <- fst <$> genPoly binPoly
      return (polynomial, Nothing)

genTestAssignment :: (Integral n, GaloisField n) => Int -> Gen (Poly n, Maybe (IntMap Bool))
genTestAssignment fieldBitWidth = do
  -- decide if we want this BinRep to be satisfiable or not
  scenario <- arbitrary
  case scenario of
    AssignmentSatisfiable -> do
      size <- choose (1, fieldBitWidth)
      binPoly <- genBinRep size
      (polynomial, (assignments, _)) <- genPoly binPoly
      return (polynomial, Just assignments)
    AssignmentConstantOutOfRange -> error "hi"

tests :: SpecWith ()
tests = describe "BinRep Detection" $ do
  describe "`detectBinRep`" $ do
    it "Prime 17" $ do
      forAll (genTestDetection 4) $ \(polynomial :: Poly (Prime 17), expected) -> do
        let actual = fst <$> detectBinRep 4 (const True) (Poly.coeffs polynomial)
        actual `shouldBe` expected

    it "GF181" $ do
      forAll (genTestDetection 180) $ \(polynomial :: Poly GF181, expected) -> do
        let actual = fst <$> detectBinRep 180 (const True) (Poly.coeffs polynomial)
        actual `shouldBe` expected

    it "Binary 7" $ do
      forAll (genTestDetection 2) $ \(polynomial :: Poly (Binary 7), expected) -> do
        let actual = fst <$> detectBinRep 2 (const True) (Poly.coeffs polynomial)
        actual `shouldBe` expected

  describe "`assignBinRep`" $ do
    it "Prime 17" $ do
      forAll (genTestAssignment 4) $ \(polynomial :: Poly (Prime 17), expected) -> do
        let actual = assignBinRep 4 (const True) polynomial
        actual `shouldBe` expected

    it "Prime 37" $ do
      forAll (genTestAssignment 5) $ \(polynomial :: Poly (Prime 37), expected) -> do
        let actual = assignBinRep 5 (const True) polynomial
        actual `shouldBe` expected

    it "GF181" $ do
      forAll (genTestAssignment 180) $ \(polynomial :: Poly GF181, expected) -> do
        let actual = assignBinRep 180 (const True) polynomial
        actual `shouldBe` expected

    it "Binary 7" $ do
      forAll (genTestAssignment 2) $ \(polynomial :: Poly (Binary 7), expected) -> do
        let actual = assignBinRep 2 (const True) polynomial
        actual `shouldBe` expected

    it "4$2 + 2$3 = 6 (mod 17)" $ do
      let polynomial = case Poly.buildEither 11 [(2, 4), (3, 2)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 17)
      let actual = assignBinRep 4 (const True) polynomial
      let expected = Just (IntMap.fromList [(2, True), (3, True)])
      actual `shouldBe` expected

    it "6$0 = 0 (mod 17)" $ do
      let polynomial = case Poly.buildEither 0 [(0, 6)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 17)
      let actual = assignBinRep 4 (const True) polynomial
      let expected = Just (IntMap.fromList [(0, False)])
      actual `shouldBe` expected

    it "6$1 = 6 (mod 17)" $ do
      let polynomial = case Poly.buildEither 11 [(1, 6)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 17)
      let actual = assignBinRep 4 (const True) polynomial
      let expected = Just (IntMap.fromList [(1, True)])
      actual `shouldBe` expected

    it "2$1 + $3 = 1 (mod 17)" $ do
      let polynomial = case Poly.buildEither 16 [(1, 2), (3, 1)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 17)
      let actual = assignBinRep 4 (const True) polynomial
      let expected = Just (IntMap.fromList [(1, False), (3, True)])
      actual `shouldBe` expected

    it "25$1 + 6$3 = 25 (mod 37)" $ do
      let polynomial = case Poly.buildEither 12 [(1, 25), (3, 6)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 37)
      let actual = assignBinRep 5 (const True) polynomial
      let expected = Just (IntMap.fromList [(1, True), (3, False)])
      actual `shouldBe` expected

    it "8$1 + 4$3 = 4 (mod 37)" $ do
      let polynomial = case Poly.buildEither 33 [(1, 8), (3, 4)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 37)
      let actual = assignBinRep 5 (const True) polynomial
      let expected = Just (IntMap.fromList [(1, False), (3, True)])
      actual `shouldBe` expected

    it "11$2 + 22$3 + 13$4 = 35 (mod 37)" $ do
      let polynomial = case Poly.buildEither 2 [(2, 11), (3, 22), (4, 13)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 37)
      let actual = assignBinRep 5 (const True) polynomial
      let expected = Just (IntMap.fromList [(2, False), (3, True), (4, True)])
      actual `shouldBe` expected

    it "$1 + 2$3 + 18$5 = 18 (mod 37)" $ do
      let polynomial = case Poly.buildEither 19 [(1, 1), (3, 2), (5, 18)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 37)
      let actual = assignBinRep 5 (const True) polynomial
      let expected = Just (IntMap.fromList [(1, False), (3, False), (5, True)])
      actual `shouldBe` expected

    it "$1 + 2$2 = 1 (Binary 7)" $ do
      let polynomial = case Poly.buildEither 1 [(2, 2), (3, 1)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Binary 7)
      let actual = assignBinRep 2 (const True) polynomial
      let expected = Just (IntMap.fromList [(2, False), (3, True)])
      actual `shouldBe` expected