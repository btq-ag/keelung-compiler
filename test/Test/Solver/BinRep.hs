{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Solver.BinRep (tests, run) where

import Data.Field.Galois (Binary, GaloisField (..), Prime)
import Data.IntMap qualified as IntMap
import Data.IntMap.Strict (IntMap)
import Data.Proxy (Proxy (..), asProxyTypeOf)
import Keelung (Width)
import Keelung.Compiler.Util (powerOf2)
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Data.U qualified as U
import Keelung.Field (GF181)
import Keelung.Solver.BinRep qualified as BinRep
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

-- | Given the number of desired coefficients, generate a BinRep
genBinRep :: (GaloisField n, Integral n) => Int -> Gen (BinRep.BinRep n)
genBinRep n = do
  -- generate excess coefficients (so that we can remove some of them later)
  signs <- vectorOf (n * 2) arbitrary -- Bool
  vars <- shuffle [0 .. n * 2 - 1] -- Var

  -- zip all of them together, and shuffle them
  -- take only `n` number of coefficients
  tuples <- take n <$> shuffle (zip signs vars)
  let zipped = zip [0 ..] tuples -- zip with powers
  let coeffs = IntMap.fromList zipped
  let (lowerBound, upperBound) = BinRep.range coeffs
  return $ BinRep.BinRep coeffs lowerBound upperBound

--------------------------------------------------------------------------------

-- | Test cases for BinRep satisfiability
data TestSatisfiability n
  = -- | construct a BinRep that can be successfully satisfied
    Satisfiable Width (Poly n) (BinRep.BinRep n)
  | -- | two coefficients have the same power
    DuplicatedCoefficients Width (Poly n)
  | -- | more than `fieldBitWidth` number of coefficients
    TooManyCoefficients Width (Poly n)
  deriving (Show, Eq)

instance (Integral n, GaloisField n) => Arbitrary (TestSatisfiability n) where
  arbitrary = do
    -- calculate the maximum allowed number of bits that fits the field
    let someFieldValue = asProxyTypeOf 0 (Proxy :: Proxy n)
    let maxAllowedBitWidth = U.widthOfInteger (fromIntegral (order someFieldValue)) - 1
    -- decide if we want this BinRep to be satisfied or not
    scenario <- arbitrary
    case scenario `mod` (3 :: Int) of
      0 -> do
        size <- choose (1, maxAllowedBitWidth)
        binPoly <- genBinRep size
        polynomial <- fst <$> genAssignment binPoly
        return $ Satisfiable maxAllowedBitWidth (asType someFieldValue polynomial) binPoly
      1 -> do
        size <- choose (2, maxAllowedBitWidth)
        binPoly <- genBinRep size
        polynomial <- fst <$> genAssignment binPoly
        -- tweak the polynomial so that it has duplicated coefficients
        let coeffs = case IntMap.toList (Poly.coeffs polynomial) of
              (power1, coeff1) : (power2, _coeff2) : rest -> (power1, coeff1) : (power2, coeff1) : rest
              _ -> error "[ panic ] genTestSatisfiability.DuplicatedCoefficients impossible"
        let polynomial' = case Poly.buildEither (Poly.constant polynomial) coeffs of
              Left _ -> error "Poly.buildEither"
              Right p -> p
        return (DuplicatedCoefficients maxAllowedBitWidth polynomial')
      _ -> do
        size <- choose (maxAllowedBitWidth + 1, maxAllowedBitWidth + 2)
        binPoly <- genBinRep size
        polynomial <- fst <$> genAssignment binPoly
        return (TooManyCoefficients maxAllowedBitWidth polynomial)
    where
      asType :: n -> Poly n -> Poly n
      asType _ b = b

-- | Execute the test cases for satisfiability
testSatisfiability :: (Integral n, GaloisField n) => TestSatisfiability n -> Expectation
testSatisfiability (Satisfiable bitWidth polynomial expected) = do
  let actual = fst <$> BinRep.isSatisfiable bitWidth (const True) (Poly.coeffs polynomial)
  actual `shouldBe` Just expected
testSatisfiability (DuplicatedCoefficients bitWidth polynomial) = do
  let actual = fst <$> BinRep.isSatisfiable bitWidth (const True) (Poly.coeffs polynomial)
  actual `shouldBe` Nothing
testSatisfiability (TooManyCoefficients bitWidth polynomial) = do
  let actual = fst <$> BinRep.isSatisfiable bitWidth (const True) (Poly.coeffs polynomial)
  actual `shouldBe` Nothing

--------------------------------------------------------------------------------

-- | Given a BinRep, generate some assignments and a valid polynomial
genAssignment :: (GaloisField n, Integral n) => BinRep.BinRep n -> Gen (Poly n, IntMap Bool)
genAssignment binPolys = do
  xs <- shuffle $ IntMap.toList $ BinRep.binPolyCoeffs binPolys
  multiplier <- suchThat arbitrary (> 0)
  values <- vectorOf (length xs) arbitrary
  -- construct the polynomial
  let (coeffs, constant) =
        foldl
          ( \(poly, c) ((power, (sign, var)), assignment) ->
              let coeff = multiplier * powerOf2 power
               in if sign
                    then ((var, coeff) : poly, c + (if assignment then 1 else 0) * coeff)
                    else ((var, -coeff) : poly, c - (if assignment then 1 else 0) * coeff)
          )
          ([], 0)
          (zip xs values)
  -- generate random assignments
  let assignments = IntMap.fromList $ zipWith (\(_power, (_sign, var)) val -> (var, val)) xs values

  case Poly.buildEither (-constant) coeffs of
    Left _ -> error "[ panic ] genAssignment failed"
    Right poly -> return (poly, assignments)

genTestAssignment :: (Integral n, GaloisField n) => Gen (Width, Poly n, IntMap Bool)
genTestAssignment = do
  -- calculate the maximum allowed number of bits that fits the field
  let someFieldValue = asProxyTypeOf 0 (Proxy :: Proxy n)
  let maxAllowedBitWidth = U.widthOfInteger (fromIntegral (order someFieldValue)) - 1
  size <- choose (1, maxAllowedBitWidth)
  (polynomial, assignment) <- genBinRep size >>= genAssignment
  return (maxAllowedBitWidth, asTypeOfFieldValue someFieldValue polynomial, assignment)
  where
    asTypeOfFieldValue :: n -> Poly n -> Poly n
    asTypeOfFieldValue _ b = b

tests :: SpecWith ()
tests = describe "BinRep" $ do
  describe "`isSatisfiable`" $ do
    it "Prime 17" $ do
      property $ \(scenario :: TestSatisfiability (Prime 17)) -> testSatisfiability scenario

    it "GF181" $ do
      property $ \(scenario :: TestSatisfiability GF181) -> testSatisfiability scenario

    it "Binary 7" $ do
      property $ \(scenario :: TestSatisfiability (Binary 7)) -> testSatisfiability scenario

  describe "`findAssignment`" $ do
    it "Prime 17" $ do
      forAll genTestAssignment $ \(fieldWidth, polynomial :: Poly (Prime 17), expected) -> do
        let actual = BinRep.findAssignment fieldWidth (const True) polynomial
        actual `shouldBe` Just expected

    it "Prime 37" $ do
      forAll genTestAssignment $ \(fieldWidth, polynomial :: Poly (Prime 37), expected) -> do
        let actual = BinRep.findAssignment fieldWidth (const True) polynomial
        actual `shouldBe` Just expected

    it "GF181" $ do
      forAll genTestAssignment $ \(fieldWidth, polynomial :: Poly GF181, expected) -> do
        let actual = BinRep.findAssignment fieldWidth (const True) polynomial
        actual `shouldBe` Just expected

    it "Binary 7" $ do
      forAll genTestAssignment $ \(fieldWidth, polynomial :: Poly (Binary 7), expected) -> do
        let actual = BinRep.findAssignment fieldWidth (const True) polynomial
        actual `shouldBe` Just expected

    it "4$2 + 2$3 = 6 (mod 17)" $ do
      let polynomial = case Poly.buildEither 11 [(2, 4), (3, 2)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 17)
      let actual = BinRep.findAssignment 4 (const True) polynomial
      let expected = Just (IntMap.fromList [(2, True), (3, True)])
      actual `shouldBe` expected

    it "6$0 = 0 (mod 17)" $ do
      let polynomial = case Poly.buildEither 0 [(0, 6)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 17)
      let actual = BinRep.findAssignment 4 (const True) polynomial
      let expected = Just (IntMap.fromList [(0, False)])
      actual `shouldBe` expected

    it "6$1 = 6 (mod 17)" $ do
      let polynomial = case Poly.buildEither 11 [(1, 6)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 17)
      let actual = BinRep.findAssignment 4 (const True) polynomial
      let expected = Just (IntMap.fromList [(1, True)])
      actual `shouldBe` expected

    it "2$1 + $3 = 1 (mod 17)" $ do
      let polynomial = case Poly.buildEither 16 [(1, 2), (3, 1)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 17)
      let actual = BinRep.findAssignment 4 (const True) polynomial
      let expected = Just (IntMap.fromList [(1, False), (3, True)])
      actual `shouldBe` expected

    it "25$1 + 6$3 = 25 (mod 37)" $ do
      let polynomial = case Poly.buildEither 12 [(1, 25), (3, 6)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 37)
      let actual = BinRep.findAssignment 5 (const True) polynomial
      let expected = Just (IntMap.fromList [(1, True), (3, False)])
      actual `shouldBe` expected

    it "8$1 + 4$3 = 4 (mod 37)" $ do
      let polynomial = case Poly.buildEither 33 [(1, 8), (3, 4)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 37)
      let actual = BinRep.findAssignment 5 (const True) polynomial
      let expected = Just (IntMap.fromList [(1, False), (3, True)])
      actual `shouldBe` expected

    it "11$2 + 22$3 + 13$4 = 35 (mod 37)" $ do
      let polynomial = case Poly.buildEither 2 [(2, 11), (3, 22), (4, 13)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 37)
      let actual = BinRep.findAssignment 5 (const True) polynomial
      let expected = Just (IntMap.fromList [(2, False), (3, True), (4, True)])
      actual `shouldBe` expected

    it "$1 + 2$3 + 18$5 = 18 (mod 37)" $ do
      let polynomial = case Poly.buildEither 19 [(1, 1), (3, 2), (5, 18)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Prime 37)
      let actual = BinRep.findAssignment 5 (const True) polynomial
      let expected = Just (IntMap.fromList [(1, False), (3, False), (5, True)])
      actual `shouldBe` expected

    it "$1 + 2$2 = 1 (Binary 7)" $ do
      let polynomial = case Poly.buildEither 1 [(2, 2), (3, 1)] of
            Left _ -> error "Poly.buildEither"
            Right p -> p :: Poly (Binary 7)
      let actual = BinRep.findAssignment 2 (const True) polynomial
      let expected = Just (IntMap.fromList [(2, False), (3, True)])
      actual `shouldBe` expected

    -- it "283$2 + $3 = 1 (Bianry 340282366920938463463374607431768211457)" $ do
    --   let polynomial = case Poly.buildEither 1 [(2, 283), (3, 1)] of
    --         Left _ -> error "Poly.buildEither"
    --         Right p -> p :: Poly (Prime 340282366920938463463374607431768211457)
    --   let actual = BinRep.findAssignment 128 (const True) polynomial
    --   let expected = Just (IntMap.fromList [(2, False), (3, True)])
    --   actual `shouldBe` expected
