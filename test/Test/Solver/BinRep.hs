{-# LANGUAGE DataKinds #-}

module Test.Solver.BinRep (tests, run) where

-- import Control.Monad
-- import Keelung hiding (compile)

import Data.Field.Galois (GaloisField, Prime)
import Data.IntMap qualified as IntMap
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Field (GF181)
import Keelung.Solver (BinPoly (..), computeBinPoly)
import Test.Hspec
import Test.QuickCheck

-- import Test.QuickCheck

run :: IO ()
run = hspec tests

-- | Test cases for BinPoly detection
data Satisfiability
  = -- | the polynomial is satisfiable
    Satisfiable
  | -- | two coefficients have the same power
    DuplicatedCoefficients
  | -- | more than `fieldBitWidth` number of coefficients
    TooManyCoefficients
  -- | -- | constant of the polynomial is out of range
  --   ConstantOutOfRange
  deriving
    ( Show,
      Eq,
      Enum
    )

instance Arbitrary Satisfiability where
  arbitrary = elements [Satisfiable, DuplicatedCoefficients, TooManyCoefficients]

-- | Given the number of desired coefficients, generate a BinPoly
genBinPoly :: Int -> Gen (BinPoly n)
genBinPoly n = do
  -- generate excess coefficients (so that we can remove some of them later)
  signs <- vectorOf (n * 2) arbitrary -- Bool
  vars <- shuffle [0 .. n * 2 - 1] -- Var
  -- zip all of them together, and shuffle them
  -- take only `n` number of coefficients
  tuples <- take n <$> shuffle (zip signs vars)
  let zipped = zip [0 ..] tuples -- zip with powers
  return $ BinPoly $ IntMap.fromList zipped

-- | Given a BinPoly, generate some assignments and a valid polynomial
genPoly :: (GaloisField n, Integral n) => BinPoly n -> Gen (Poly n)
genPoly binPolys = do
  xs <- shuffle $ IntMap.toList $ binPolyCoeffs binPolys
  multiplier <- suchThat arbitrary (> 0)
  assignments <- vectorOf (length xs) arbitrary
  let (coeffs, _lower, constant, _upper) =
        foldl
          ( \(poly, l, c, u) ((power, (sign, var)), assignment) ->
              let coeff = if sign then multiplier * 2 ^ power else -multiplier * (2 ^ power)
               in ((var, coeff) : poly, l, c + (if assignment then 1 else 0) * coeff, u + coeff)
          )
          ([], 0 :: Int, 0, 0)
          (zip xs assignments)
  case Poly.buildEither (-constant) coeffs of
    Left _ -> error "Poly.buildEither"
    Right poly -> return poly

genTestCase :: (Integral n, GaloisField n) => Int -> Gen (Poly n, Maybe (BinPoly n))
genTestCase fieldBitWidth = do
  -- decide if we want this polynomial to be satisfiable or not
  satisfiability <- arbitrary
  case satisfiability of
    Satisfiable -> do
      size <- choose (1, fieldBitWidth)
      binPoly <- genBinPoly size
      polynomial <- genPoly binPoly
      return (polynomial, Just binPoly)
    DuplicatedCoefficients -> do
      size <- choose (2, fieldBitWidth)
      binPoly <- genBinPoly size
      polynomial <- genPoly binPoly
      -- tweak the polynomial so that it has duplicated coefficients
      let coeffs = case IntMap.toList (Poly.coeffs polynomial) of
            (power1, coeff1) : (power2, _coeff2) : rest -> (power1, coeff1) : (power2, coeff1) : rest
            _ -> error "[ panic ] genPoly.DuplicatedCoefficients impossible"
      let polynomial' = case Poly.buildEither (Poly.constant polynomial) coeffs of
            Left _ -> error "Poly.buildEither"
            Right p -> p
      return (polynomial', Nothing)
    TooManyCoefficients -> do
      size <- choose (fieldBitWidth + 1, fieldBitWidth + 2)
      binPoly <- genBinPoly size
      polynomial <- genPoly binPoly
      return (polynomial, Nothing)
    -- ConstantOutOfRange -> do
    --   size <- choose (1, fieldBitWidth)
    --   binPoly <- genBinPoly size

    --   let (lowerBound, upperBound) = rangeOfBinPoly binPoly
    --   constant <-
    --     if toInteger lowerBound < toInteger upperBound
    --       then do
    --         -- the domain of the polynomial ranges from [lowerBound, upperBound]
    --         leftOrRight <- arbitrary
    --         if leftOrRight
    --           then choose (0, lowerBound - 1)
    --           else return $ upperBound + 1
    --       else -- the domain of the polynomial ranges from [0 .. lowerBound] and [upperBound .. maxBound]
    --         choose (lowerBound + 1, upperBound - 1)

    --   polynomial <- genPoly binPoly
    --   -- tweak the polynomial so that it has duplicated coefficients
    --   let polynomial' = Poly.addConstant (constant - Poly.constant polynomial) polynomial
    --   return (polynomial', Nothing)

tests :: SpecWith ()
tests = describe "BinRep Detection" $ do
  -- let polynomial = case Poly.buildEither (-8) [(0, 1), (1, 2), (2, 4)] of
  --       Left _ -> error "Poly.buildEither"
  --       Right p -> p :: Poly (Prime 11)
  -- let actual = computeBinPoly 3 (const True) polynomial
  -- let expected = Nothing
  -- it "unsatisfiable" $ do
  --   actual `shouldBe` expected

  -- it "`computeBinPoly` : all positvie / mod 11" $ do
  --   forAll (genBinPoly 3 [True]) $ \(binPoly, powerSignIntMap) -> do
  --     -- testing with [(var, sign)] pairs
  --     let actual = computeBinPoly 3 (const True) polynomial
  --     let expected = powerSignIntMap
  --     actual `shouldBe` expected

  it "`computeBinPoly` : mod 17" $ do
    forAll (genTestCase 4) $ \(polynomial :: Poly (Prime 17), binPoly) -> do
      let actual = computeBinPoly 4 (const True) (Poly.coeffs polynomial)
      let expected = binPoly
      actual `shouldBe` expected

  it "`computeBinPoly` : mod GF181" $ do
    forAll (genTestCase 180) $ \(polynomial :: Poly GF181, binPoly) -> do
      let actual = computeBinPoly 180 (const True) (Poly.coeffs polynomial)
      let expected = binPoly
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