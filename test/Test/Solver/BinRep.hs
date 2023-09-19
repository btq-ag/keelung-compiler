{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Solver.BinRep (tests, run) where

-- import Control.Monad
-- import Keelung hiding (compile)

import Data.Field.Galois (GaloisField, Prime)
import Data.IntMap qualified as IntMap
import Data.IntMap.Strict (IntMap)
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Field (GF181)
import Keelung.Solver (BinRep (..), assignBinRep, detectBinRep, powerOf2, rangeOfBinRep)
import Test.Hspec
import Test.QuickCheck

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
  arbitrary = elements [AssignmentSatisfiable]

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

genTestAssignment :: (Integral n, GaloisField n) => Int -> Gen (Poly n, Maybe (IntMap Bool, IntMap n))
genTestAssignment fieldBitWidth = do
  -- decide if we want this BinRep to be satisfiable or not
  scenario <- arbitrary
  case scenario of
    AssignmentSatisfiable -> do
      size <- choose (1, fieldBitWidth)
      binPoly <- genBinRep size
      (polynomial, (assignments, _)) <- genPoly binPoly
      return (polynomial, Just (assignments, mempty))
    AssignmentConstantOutOfRange -> error "hi"

tests :: SpecWith ()
tests = describe "BinRep Detection" $ do
  describe "`detectBinRep`" $ do
    it "Prime 17" $ do
      forAll (genTestDetection 4) $ \(polynomial :: Poly (Prime 17), binPoly) -> do
        let actual = fst <$> detectBinRep 4 (const True) (Poly.coeffs polynomial)
        let expected = binPoly
        actual `shouldBe` expected

    it "GF181" $ do
      forAll (genTestDetection 180) $ \(polynomial :: Poly GF181, binPoly) -> do
        let actual = fst <$> detectBinRep 180 (const True) (Poly.coeffs polynomial)
        let expected = binPoly
        actual `shouldBe` expected

  describe "`assignBinRep`" $ do
    it "Prime 17" $ do
      forAll (genTestAssignment 4) $ \(polynomial :: Poly (Prime 17), assignments) -> do
        let actual = assignBinRep 4 (const True) polynomial
        let expected = assignments
        actual `shouldBe` expected

    it "Prime 37" $ do
      forAll (genTestAssignment 5) $ \(polynomial :: Poly (Prime 37), assignments) -> do
        let actual = assignBinRep 5 (const True) polynomial
        let expected = assignments
        actual `shouldBe` expected

    it "GF181" $ do
      forAll (genTestAssignment 180) $ \(polynomial :: Poly GF181, assignments) -> do
        let actual = assignBinRep 180 (const True) polynomial
        let expected = assignments
        actual `shouldBe` expected

    it "4$2 + 2$3 = 6 (mod 17)" $ do
      let polynomial = case Poly.buildEither 11 [(2, 4), (3, 2)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 17)
      let actual = assignBinRep 4 (const True) polynomial
      let expected = Just (IntMap.fromList [(2, True), (3, True)], mempty)
      actual `shouldBe` expected

    it "6$0 = 0 (mod 17)" $ do
      let polynomial = case Poly.buildEither 0 [(0, 6)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 17)
      let actual = assignBinRep 4 (const True) polynomial
      let expected = Just (IntMap.fromList [(0, False)], mempty)
      actual `shouldBe` expected

    it "6$1 = 6 (mod 17)" $ do
      let polynomial = case Poly.buildEither 11 [(1, 6)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 17)
      let actual = assignBinRep 4 (const True) polynomial
      let expected = Just (IntMap.fromList [(1, True)], mempty)
      actual `shouldBe` expected

    it "2$1 + $3 = 1 (mod 17)" $ do
      let polynomial = case Poly.buildEither 16 [(1, 2), (3, 1)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 17)
      let actual = assignBinRep 4 (const True) polynomial
      let expected = Just (IntMap.fromList [(1, False), (3, True)], mempty)
      actual `shouldBe` expected

    it "25$1 + 6$3 = 25 (mod 37)" $ do
      let polynomial = case Poly.buildEither 12 [(1, 25), (3, 6)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 37)
      let actual = assignBinRep 5 (const True) polynomial
      let expected = Just (IntMap.fromList [(1, True), (3, False)], mempty)
      actual `shouldBe` expected

    it "8$1 + 4$3 = 4 (mod 37)" $ do
      let polynomial = case Poly.buildEither 33 [(1, 8), (3, 4)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 37)
      let actual = assignBinRep 5 (const True) polynomial
      let expected = Just (IntMap.fromList [(1, False), (3, True)], mempty)
      actual `shouldBe` expected

    it "11$2 + 22$3 + 13$4 = 35 (mod 37)" $ do
      let polynomial = case Poly.buildEither 2 [(2, 11), (3, 22), (4, 13)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 37)
      let actual = assignBinRep 5 (const True) polynomial
      let expected = Just (IntMap.fromList [(2, False), (3, True), (4, True)], mempty)
      actual `shouldBe` expected

    it "$1 + 2$3 + 18$5 = 18 (mod 37)" $ do
      let polynomial = case Poly.buildEither 19 [(1, 1), (3, 2), (5, 18)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 37)
      let actual = assignBinRep 5 (const True) polynomial
      let expected = Just (IntMap.fromList [(1, False), (3, False), (5, True)], mempty)
      actual `shouldBe` expected

    it "-$B0 - 2$F10 = 0 (mod 37) EVEN or ODD" $ do
      let polynomial = case Poly.buildEither 0 [(0, -1), (10, -2)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 37)
      let actual = assignBinRep 5 (< 10) polynomial -- let $0 be Boolean and $10 be Field
      let expected = Just (IntMap.fromList [(0, False)], IntMap.fromList [(10, 0)])
      actual `shouldBe` expected

    it "-$B0 - 2$F10 = -3 (mod 37) EVEN or ODD" $ do
      let polynomial = case Poly.buildEither 3 [(0, -1), (10, -2)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 37)
      let actual = assignBinRep 5 (< 10) polynomial -- let $0 be Boolean and $10 be Field
      let expected = Just (IntMap.fromList [(0, True)], IntMap.fromList [(10, 1)])
      actual `shouldBe` expected

    it "$B0 + 2$F10 = 1 (mod 37) EVEN or ODD" $ do
      let polynomial = case Poly.buildEither (-1) [(0, 1), (10, 2)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 37)
      let actual = assignBinRep 5 (< 10) polynomial -- let $0 be Boolean and $10 be Field
      let expected = Just (IntMap.fromList [(0, True)], IntMap.fromList [(10, 0)])
      actual `shouldBe` expected

    it "$B0 - 2$F10 = 1 (mod 13) EVEN or ODD" $ do
      let polynomial = case Poly.buildEither (-1) [(0, 1), (10, -2)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 13)
      let actual = assignBinRep 3 (< 10) polynomial -- let $0 be Boolean and $10 be Field
      let expected = Just (IntMap.fromList [(0, True)], IntMap.fromList [(10, 0)])
      actual `shouldBe` expected

    it "$B0 - 2$F10 = 0 (mod 13) EVEN or ODD" $ do
      let polynomial = case Poly.buildEither 0 [(0, 1), (10, -2)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 13)
      let actual = assignBinRep 3 (< 10) polynomial -- let $0 be Boolean and $10 be Field
      let expected = Just (IntMap.fromList [(0, False)], IntMap.fromList [(10, 0)])
      actual `shouldBe` expected

    it "$B0 - 2$F10 = -1 (mod 13) EVEN or ODD" $ do
      let polynomial = case Poly.buildEither 1 [(0, 1), (10, -2)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 13)
      let actual = assignBinRep 3 (< 10) polynomial -- let $0 be Boolean and $10 be Field
      let expected = Just (IntMap.fromList [(0, True)], IntMap.fromList [(10, 1)])
      actual `shouldBe` expected
      
    it "-$B0 + 2$F10 = 1 (mod 13) EVEN or ODD" $ do
      let polynomial = case Poly.buildEither (-1) [(0, -1), (10, 2)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 13)
      let actual = assignBinRep 3 (< 10) polynomial -- let $0 be Boolean and $10 be Field
      let expected = Just (IntMap.fromList [(0, True)], IntMap.fromList [(10, 1)])
      actual `shouldBe` expected

-- it "$0 + 2$1 + 4$2 = 1 (mod 11)" $ do
--   let polynomial = case Poly.buildEither (-1) [(0, 1), (1, 2), (2, 4)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly (Prime 11)
--   let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
--   let expected = Just $ IntMap.fromList [(2, False), (1, False), (0, True)]
--   actual `shouldBe` expected

-- it "$0 + 2$1 + 4$2 = 5 (mod 11)" $ do
--   let polynomial = case Poly.buildEither (-5) [(0, 1), (1, 2), (2, 4)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly (Prime 11)
--   let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
--   let expected = Just $ IntMap.fromList [(2, True), (1, False), (0, True)]
--   actual `shouldBe` expected

-- it "$0 - 2$1 + 4$2 = 5 (mod 11)" $ do
--   let polynomial = case Poly.buildEither (-5) [(0, 1), (1, -2), (2, 4)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly (Prime 11)
--   let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
--   let expected = Just $ IntMap.fromList [(2, True), (1, False), (0, True)]
--   actual `shouldBe` expected

-- it "$0 - 2$1 + 4$2 = 3 (mod 11)" $ do
--   let polynomial = case Poly.buildEither (-3) [(0, 1), (1, -2), (2, 4)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly (Prime 11)
--   let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
--   let expected = Just $ IntMap.fromList [(2, True), (1, True), (0, True)]
--   actual `shouldBe` expected

-- it "2$0 - 4$1 + 8$2 = 6 (mod 11)" $ do
--   let polynomial = case Poly.buildEither (-6) [(0, 2), (1, -4), (2, 8)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly (Prime 11)
--   let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
--   let expected = Just $ IntMap.fromList [(2, True), (1, True), (0, True)]
--   actual `shouldBe` expected

-- it "3$0 - 6$1 + $2 = 9 (mod 11)" $ do
--   let polynomial = case Poly.buildEither (-9) [(0, 3), (1, -6), (2, 1)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly (Prime 11)
--   let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
--   let expected = Just $ IntMap.fromList [(2, True), (1, True), (0, True)]
--   actual `shouldBe` expected

-- it "3$0 + $1 - 6$2 = 9 (mod 11)" $ do
--   let polynomial = case Poly.buildEither (-9) [(0, 3), (1, 1), (2, -6)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly (Prime 11)
--   let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
--   let expected = Just $ IntMap.fromList [(1, True), (2, True), (0, True)]
--   actual `shouldBe` expected

-- it "9$0 + 10$1 + 7$2 = 10 (mod 11)" $ do
--   let polynomial = case Poly.buildEither (-10) [(0, 9), (1, 10), (2, 7)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly (Prime 11)
--   let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
--   let expected = Just $ IntMap.fromList [(2, False), (1, True), (0, False)]
--   actual `shouldBe` expected

-- it "$0 - $1 = 0 (mod 11)" $ do
--   let polynomial = case Poly.buildEither 0 [(0, 1), (1, -1)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly (Prime 11)
--   let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
--   let expected = Nothing
--   actual `shouldBe` expected

-- it "$0 - $1 = 0 (mod 17)" $ do
--   let polynomial = case Poly.buildEither 0 [(0, 1), (1, -1)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly (Prime 17)
--   let actual = IntMap.fromList <$> detectBinRep 4 (const True) polynomial
--   let expected = Nothing
--   actual `shouldBe` expected

-- it "$0 = 1 (mod 11)" $ do
--   let polynomial = case Poly.buildEither (-1) [(0, 1)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly (Prime 11)
--   let actual = IntMap.fromList <$> detectBinRep 3 (const True) polynomial
--   let expected = Just $ IntMap.fromList [(0, True)]
--   actual `shouldBe` expected

-- it "-16$17 + $24 + 2$25 + 4$26 + 8$27 - $28 - 2$29 - 4$30 - 8$31 = -7 (mod GF181)" $ do
--   let polynomial = case Poly.buildEither 7 [(17, -16), (24, 1), (25, 2), (26, 4), (27, 8), (28, -1), (29, -2), (30, -4), (31, -8)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly GF181
--   let actual = IntMap.fromList <$> detectBinRep 180 (const True) polynomial
--   let expected = Nothing
--   actual `shouldBe` expected

-- it "4$21 - $30 + -2$31 = 2 (mod 31)" $ do
--   let polynomial = case Poly.buildEither 2 [(21, 4), (30, -1), (31, -2)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly (Prime 31)
--   let actual = IntMap.fromList <$> detectBinRep 4 (const True) polynomial
--   let expected = Just $ IntMap.fromList [(21, True), (30, False), (31, True)]
--   actual `shouldBe` expected

-- it "$0 + 2$1 + 4$2 = 6 (mod 17)" $ do
--   let polynomial = case Poly.buildEither (-6) [(0, 1), (1, 2), (2, 4)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly (Prime 17)
--   let actual = IntMap.fromList <$> detectBinRep 4 (const True) polynomial
--   let expected = Just $ IntMap.fromList [(2, True), (1, True), (0, False)]
--   actual `shouldBe` expected

-- it "$0 + 2$1 + 4$2 + 8$3 + 16$4 - 32$5 = 6 (mod GF181)" $ do
--   let polynomial = case Poly.buildEither (-6) [(0, 1), (1, 2), (2, 4), (3, 8), (4, 16), (5, -32)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly GF181
--   let actual = IntMap.fromList <$> detectBinRep 180 (const True) polynomial
--   let expected = Just $ IntMap.fromList [(0, False), (1, True), (2, True), (3, False), (4, False), (5, False)]
--   actual `shouldBe` expected

-- it "32$20 - $31 + -2$32 + -4$33 + -8$34 + -16$35 = -6 (mod GF181)" $ do
--   let polynomial = case Poly.buildEither 6 [(31, -1), (32, -2), (33, -4), (34, -8), (35, -16), (20, 32)] of
--         Left _ -> error "Poly.buildEither"
--         Right p -> p :: Poly GF181
--   let actual = IntMap.fromList <$> detectBinRep 180 (const True) polynomial
--   let expected = Just $ IntMap.fromList [(31, False), (32, True), (33, True), (34, False), (35, False), (20, False)]
--   actual `shouldBe` expected