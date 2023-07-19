{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant if" #-}
module Keelung.Solver.BinRep where

import Control.Monad.RWS
import Data.Bits (xor)
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Solver.Monad
import Keelung.Syntax (Var, Width)

-- | Trying to reduce a BinRep constraint
data FoldState n = Start | Failed | Continue n [Candidate n] deriving (Eq, Show)

-- | Reduce binary representations
shrinkBinRep :: (GaloisField n, Integral n) => Result (Constraint n) -> M n (Result (Constraint n))
shrinkBinRep NothingToDo = return NothingToDo
shrinkBinRep Eliminated = return Eliminated
shrinkBinRep (Shrinked polynomial) = return (Shrinked polynomial)
shrinkBinRep (Stuck (AddConstraint polynomial)) = do
  Env _ boolVarRanges fieldBitWidth <- ask
  let isBoolean var = case IntMap.lookupLE var boolVarRanges of
        Nothing -> False
        Just (index, len) -> var < index + len
  case assignBinRep fieldBitWidth isBoolean polynomial of
    Nothing -> return (Stuck (AddConstraint polynomial))
    Just assignments -> do
      tryLog $ LogBinRepDetection polynomial (IntMap.toList assignments)
      -- we have a binary representation
      -- we can now assign the variables
      forM_ (IntMap.toList assignments) $ \(var, val) -> do
        bindVar "bin rep" var (if val then 1 else 0)
      return Eliminated
shrinkBinRep (Stuck polynomial) = return (Stuck polynomial)

-- | Given a mapping of (Int, (Bool, Var)) pairs, where the Int indicates the power of 2, and the Bool indicates whether the coefficient is positive or negative
--   and an Integer, derive coefficients (Boolean) for each of these variables such that the sum of the coefficients times the powers of 2 is equal to the Integer
deriveAssignments :: (GaloisField n, Integral n) => (Integer, Integer) -> n -> IntMap (Bool, Var) -> Maybe (IntMap Bool)
deriveAssignments (lowerBound, upperBound) rawConstant polynomial =
  let -- should flip the sign of everything (coefficients and constant) if the constant is outside the bounds of the polynomial
      shouldFlip = lowerBound > upperBound && fromIntegral rawConstant >= lowerBound
      constant = if shouldFlip then fromIntegral (-rawConstant) else fromIntegral rawConstant
      (result, remainder) = IntMap.foldlWithKey' (go shouldFlip) (mempty, constant) polynomial
   in if remainder == 0
        then Just result
        else Nothing
  where
    go :: Bool -> (IntMap Bool, Integer) -> Int -> (Bool, Var) -> (IntMap Bool, Integer)
    go flipped (acc, c) power (sign, var) =
      let deduct = flipped `xor` sign -- remove power of 2 from constant
       in if Data.Bits.testBit c power
            then (IntMap.insert var True acc, c + if deduct then -(2 ^ power) else 2 ^ power)
            else (IntMap.insert var False acc, c)

-- | Watch out for a stuck R1C, and see if it's a binary representation
--
--   Property:
--    For a field of order `n`, let `k = floor(log2(n))`, i.e., the number of bits that can be fit into a field element.
--    1. There can be at most `k` coefficients that are multiples of powers of 2 if the polynomial is a binary representation.
--    2. These coefficients cannot be too far apart, i.e., the quotient of any 2 coefficients cannot be greater than `2^(k-1)`.
--    3. For any 2 coefficients `a` and `b`, either `a / b` or `b / a` must be a power of 2 smaller than `2^k`.
assignBinRep :: (GaloisField n, Integral n) => Width -> (Var -> Bool) -> Poly n -> Maybe (IntMap Bool)
assignBinRep fieldBitWidth isBoolean polynomial =
  if IntMap.size (Poly.coeffs polynomial) > fromIntegral fieldBitWidth
    then Nothing
    else case detectBinRep fieldBitWidth isBoolean (Poly.coeffs polynomial) of
      Nothing -> Nothing
      Just (binPoly, multiplier) ->
        case IntMap.lookupMin (binPolyCoeffs binPoly) of
          Nothing -> Just mempty
          Just (minPower, _) ->
            let constant = (-Poly.constant polynomial / multiplier)
             in if minPower < 0
                  then
                    deriveAssignments
                      (toInteger (binPolyLowerBound binPoly * (2 ^ (-minPower))), toInteger (binPolyUpperBound binPoly * (2 ^ (-minPower))))
                      (constant * (2 ^ (-minPower)))
                      (IntMap.mapKeys (\i -> i - minPower) (binPolyCoeffs binPoly))
                  else
                    deriveAssignments
                      (toInteger (binPolyLowerBound binPoly), toInteger (binPolyUpperBound binPoly))
                      constant
                      (binPolyCoeffs binPoly)

-- | Polynomial with coefficients that are multiples of powers of 2
data BinRep n = BinRep
  { -- | Coefficients are stored as (sign, var) pairs
    binPolyCoeffs :: IntMap (Bool, Var),
    binPolyLowerBound :: n,
    binPolyUpperBound :: n
  }
  deriving (Show)

-- | 2 BinReps are equal if they are equal up to some shifts and negations
instance (GaloisField n, Integral n) => Eq (BinRep n) where
  binRepA == binRepB =
    let flippedA = flipBinRep binRepA
        flippedB = flipBinRep binRepB
     in if IntMap.keys flippedA == IntMap.keys flippedB
          then
            let pairsA = IntMap.elems flippedA
                pairsB = IntMap.elems flippedB
             in let diff = case (pairsA, pairsB) of
                      ([], []) -> 1
                      ((aSign, aPower) : _, (bSign, bPower) : _) ->
                        let powerDiff = powerOf2 (aPower - bPower)
                         in if aSign == bSign then powerDiff else -powerDiff
                      _ -> error "BinRep Eq impossible"
                 in fmap normalize flippedA == fmap ((diff *) . normalize) flippedB
          else False
    where
      -- BinRep are power-indexed IntMaps
      -- we flip them into variable-indexed IntMaps so that we can compare them
      flipBinRep :: BinRep n -> IntMap (Bool, Int)
      flipBinRep (BinRep xs _ _) = IntMap.fromList $ fmap (\(i, (b, v)) -> (v, (b, i))) (IntMap.toList xs)

      normalize :: (GaloisField n, Integral n) => (Bool, Int) -> n
      normalize (True, power) = powerOf2 power
      normalize (False, power) = -(powerOf2 power)

powerOf2 :: (GaloisField n, Integral n) => Int -> n
powerOf2 n
  | n < 0 = recip (2 ^ (-n))
  | otherwise = 2 ^ n

rangeOfBinRep :: (GaloisField n, Integral n) => IntMap (Bool, Var) -> (n, n)
rangeOfBinRep = IntMap.foldlWithKey' go (0, 0)
  where
    go :: (GaloisField n, Integral n) => (n, n) -> Int -> (Bool, Var) -> (n, n)
    go (lowerBound, upperBound) power (True, _) = (lowerBound, upperBound + powerOf2 power)
    go (lowerBound, upperBound) power (False, _) = (lowerBound - powerOf2 power, upperBound)

type Candidate n = (IntMap (Bool, Var), n, n, n)

-- | Computes a BinRep and a multiplier: BinRep * multiplier = input polynomial
detectBinRep :: (GaloisField n, Integral n) => Width -> (Var -> Bool) -> IntMap n -> Maybe (BinRep n, n)
detectBinRep fieldBitWidth isBoolean xs =
  case IntMap.foldlWithKey' go Start xs of
    Start -> Nothing
    Failed -> Nothing
    Continue _ [] -> Nothing -- no answer
    Continue _ ((coeffMap, lowerBound, upperBound, multiplier) : _) -> Just (BinRep coeffMap lowerBound upperBound, multiplier)
  where
    go :: (GaloisField n, Integral n) => FoldState n -> Var -> n -> FoldState n
    go Start var coeff =
      if isBoolean var
        then -- since this is the first coefficient, we can always assume that it's a power of 2
          Continue coeff [(IntMap.singleton 0 (True, var), 0, 1, coeff)]
        else Failed
    go Failed _ _ = Failed
    go (Continue picked coeffMaps) var coeff =
      if isBoolean var
        then Continue picked (coeffMaps >>= checkCoeffDiff var picked coeff)
        else Failed

    -- see if a coefficient is a multiple of a power of 2 of the picked coefficient
    -- we need to examine all 4 combinations:
    --  1. `coeff / picked`
    --  2. `picked / coeff`
    --  3. `-coeff / picked`
    --  4. `picked / -coeff`
    checkCoeffDiff :: (GaloisField n, Integral n) => Var -> n -> n -> Candidate n -> [Candidate n]
    checkCoeffDiff var picked coeff (coeffMap, lowerBound, upperBound, multiplier) = do
      pickedAsDenominator <- [True, False] -- whether `picked` is the denominator
      negated <- [True, False] -- whether the coefficient is negated
      let coeff' = if negated then -coeff else coeff
      let diff = if pickedAsDenominator then coeff' / picked else picked / coeff'
      case isPowerOf2 fieldBitWidth diff of
        Just power -> do
          let power' = if pickedAsDenominator then power else -power
          guard (guardPower coeffMap power')
          guard (not (IntMap.member power' coeffMap))
          let lowerBound' = if negated then lowerBound - powerOf2 power' else lowerBound
          let upperBound' = if negated then upperBound else upperBound + powerOf2 power'
          return (IntMap.insert power' (not negated, var) coeffMap, lowerBound', upperBound', multiplier)
        Nothing -> mzero

    -- because the quotient of any 2 coefficients cannot be greater than `2^(k-1)`,
    -- we need to check if the power to be inserted is too large or too small
    guardPower :: IntMap (Bool, Var) -> Int -> Bool
    guardPower coeffs power =
      let k = fromIntegral fieldBitWidth
       in -- because the quotient of any 2 coefficients cannot be greater than `2^(k-1)`,
          -- we need to check if the power to be inserted is too large or too small
          case IntMap.lookupMin coeffs of
            Nothing -> False
            Just (minPower, _) -> case IntMap.lookupMax coeffs of
              Nothing -> False
              Just (maxPower, _) -> not (power > maxPower && power - minPower > k - 1 || power < minPower && maxPower - power > k - 1)

-- | See if a coefficient is a power of 2 (except for 2^0)
isPowerOf2 :: (GaloisField n, Integral n) => Width -> n -> Maybe Int
isPowerOf2 _ 1 = Nothing
isPowerOf2 fieldBitWidth coeff =
  case check (toInteger coeff) of
    Nothing -> Nothing
    Just 0 -> Nothing
    Just result ->
      if result >= fieldBitWidth
        then Nothing
        else Just result
  where
    -- Speed this up
    check :: Integer -> Maybe Int
    check 2 = Just 1
    check 4 = Just 2
    check 8 = Just 3
    check 16 = Just 4
    check n =
      let expected = floor (logBase 2 (fromInteger n) :: Double)
       in if n == 2 ^ expected
            then Just expected
            else Nothing

-- isPowerOf2 :: (GaloisField n, Integral n) => n -> Maybe (Bool, Int)
-- isPowerOf2 (-2) = Just (False, 1)
-- isPowerOf2 (-1) = Just (False, 0)
-- isPowerOf2 1 = Just (True, 0)
-- isPowerOf2 2 = Just (True, 1)
-- isPowerOf2 coeff =
--   let asInteger = toInteger coeff
--    in if even asInteger
--         then (True,) <$> check asInteger
--         else (False,) <$> check (negate (fromIntegral (order coeff) - fromIntegral coeff))
--   where
--     -- Speed this up
--     check :: Integer -> Maybe Int
--     check n =
--       let expected = floor (logBase 2 (fromInteger (abs n)) :: Double)
--        in if abs n == 2 ^ expected
--             then Just expected
--             else Nothing
