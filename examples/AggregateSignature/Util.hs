module AggregateSignature.Util where

import Data.Array
import Data.Bits (testBit)
import Data.Field.Galois (GaloisField)
import Data.Semiring (Semiring (..))
import System.Random

--------------------------------------------------------------------------------

-- coefficients of terms of signatures
type Signature n = Array Int n

type PublicKey n = Array Int n

--------------------------------------------------------------------------------

-- | Parameters for Aggregate Signature
data Param n = Param
  { paramDimension :: Int,
    paramNumberOfSignatures :: Int,
    paramSetup :: Setup n,
    paramSettings :: Settings
  }

--------------------------------------------------------------------------------

q :: (Integral n, Num n) => n
q = 12289

-- Note: allocation of inputs in Jackie's implementation
--
--  nT  : coefficients of signatures  <multiplication> <bit value> <square>
--  nT  : "remainders"                <multiplication> <summation>
--  nT  : "quotients"                 <multiplication>
--  14nT: bitstring                   <bit value> <bit range> <bit check>
--  nT  : most significant 2 bits     <bit range>                 (unnecessary)
--  nT  : square of coeffs of sigs    <square> <length>
--  T   : sum(squares) % Q            <square> <length>

-- | Setups for the system
data Setup n = Setup
  { -- | nT: Coefficients of terms of public keys
    setupPublicKeys :: [PublicKey n],
    -- | nT: Coefficients of terms of signatures
    setupSignatures :: [Signature n],
    -- | nT: "Remainders"
    setupSigRemainders :: [Array Int n],
    -- | nT: "Quotients"
    setupSigQuotients :: [Array Int n],
    -- | n: Coefficients of terms of Aggregate signature
    setupAggSigs :: Signature n,
    -- | 14nT: Bit strings of signatures
    setupSigBitStrings :: [[[n]]],
    -- | Squares of coefficients of signatures
    setupSigSquares :: [Signature n],
    -- |
    setupSigLengths :: [n]
  }

-- | Settings for enabling/disabling different part of Aggregate Signature
data Settings = Settings
  { enableAggChecking :: Bool,
    enableSizeChecking :: Bool,
    enableLengthChecking :: Bool
  }

--------------------------------------------------------------------------------

makeParam :: (Random n, GaloisField n, Integral n, Num n) => Int -> Int -> Int -> Settings -> Param n
makeParam dimension t seed settings =
  Param
    { paramDimension = dimension,
      paramNumberOfSignatures = t,
      paramSetup = Setup publicKeys signatures remainders quotients aggSig bisStrings sigSquares sigLengths,
      paramSettings = settings
    }
  where
    -- raw input numbers range from of `-q/2` to `q/2`
    -- this function move the negative numbers from [ -q/2 , 0 ) to [ q/2 , q ) by adding `q`
    -- rectify :: (Integral n, Num n, Eq n) => n -> n
    -- rectify n = if signum n == -1 then n + q else n

    -- domain of coefficients of signatures: [0, 12289)
    signatures :: Num n => [Signature n]
    signatures = map (fmap (fromIntegral . (`mod` 12289))) arraysForSignatures

    -- domain of terms of public keys: [0, 12289)
    publicKeys :: Num n => [PublicKey n]
    publicKeys = map (fmap (fromIntegral . (`mod` 12289))) arraysForPublicKeys

    (remainders, quotients) = computeRemsAndQuots dimension signatures publicKeys

    -- NOTE: somehow generating new `StdGen` from IO would result in segmentation fault (possibly due to FFI)

    -- generate fake numbers for populating fake signatures & public keys
    randomNumbers :: [Int]
    randomNumbers = take (dimension * t * 2) $ randoms (mkStdGen (succ seed))

    -- split random numbers into small arrays (of size `dimension`) for fake signatures & public keys
    arraysForSignatures :: [Array Int Int]
    arraysForPublicKeys :: [Array Int Int]
    (arraysForSignatures, arraysForPublicKeys) = splitAt t $ splitListIntoArrays dimension randomNumbers

    aggSig = listArray (0, dimension - 1) $ map ithSum [0 .. dimension - 1]
      where
        ithSum i = sum $ map (! i) remainders

    bisStrings = map (toBitStrings . elems) signatures

    toBitStrings :: GaloisField n => [Integer] -> [[n]]
    toBitStrings = map (toListLE . toInteger)

    {-# INLINE toListLE #-}
    toListLE :: GaloisField n => Integer -> [n]
    toListLE b = fmap (toGF . testBit b) [0 .. 13]

    toGF :: GaloisField n => Bool -> n
    toGF True = one
    toGF False = zero

    sigSquares = map (fmap (\x -> x * x)) signatures
    sigLengths = map sum sigSquares

--    let S be the signature and P be the public key
--    let Q = q - P
--
--        j     0       1       2      ...      510     511
--    i   ┌──────────────────────────  ...  ────────────────────┐
--        │                                                     │
--    0   │   S₀P₀    S₁Q₅₁₁  S₂Q₅₁₀   ...    S₅₁₀Q₂  S₅₁₁Q₁    │
--        │                                                     │
--    1   │   S₀P₁    S₁P₀    S₂Q₅₁₁   ...    S₅₁₀Q₃  S₅₁₁Q₂    │
--        │                                                     │
--    2   │   S₀P₂    S₁P₁    S₂P₀     ...    S₅₁₀Q₄  S₅₁₁Q₃    │
--        │                                                     │
--    .   │   .       .       .        .      .       .         .
--    .   │   .       .       .         .     .       .         .
--    .   │   .       .       .          .    .       .         .
--        │                                                     │
--   510  │   S₀P₅₁₀  S₁P₅₀₉  S₂P₅₀₈   ...    S₅₁₀P₀  S₅₁₁Q₅₁₁  │
--        │                                                     │
--   511  │   S₀P₅₁₁  S₁P₅₁₀  S₂P₅₀₉   ...    S₅₁₀P₁  S₅₁₁P₀    │
--        │                                                     │
--        └──────────────────────────  ...  ────────────────────┘

-- Get an array of remainders and an array of quotients from a signature and a public key
computeRemsAndQuots :: (Integral n, Num n, Show n) => Int -> [Signature n] -> [PublicKey n] -> ([Array Int n], [Array Int n])
computeRemsAndQuots dimension signatures publicKeys = unzip $ zipWith (computeRemsAndQuot dimension) signatures publicKeys

computeRemsAndQuot :: (Integral n, Num n, Show n) => Int -> Signature n -> PublicKey n -> (Array Int n, Array Int n)
computeRemsAndQuot dimension signature publicKey =
  let (remainders, quotients) = unzip [handleRow i | i <- [0 .. dimension - 1]]
   in (listArray (0, dimension - 1) remainders, listArray (0, dimension - 1) quotients)
  where
    -- NOTE: forall x, y. x `mod` y = 0 on any Galois field
    -- we need to convert these numbers to Integers 
    -- to get the remainders and quotients we want 
    handleRow i =
      let total = sum [lookupSigPk i j | j <- [0 .. dimension - 1]]
       in ( fromInteger $ toInteger total `mod` (q :: Integer),
            fromInteger $ toInteger total `div` (q :: Integer)
          )

    lookupSigPk i j =
      signature ! j
        * ( if i < j
              then q - (publicKey ! (dimension + i - j))
              else publicKey ! (i - j)
          )

--------------------------------------------------------------------------------

-- Allocation of inputs when all components are enabled
--
--  size    inputs                      components that need them
----------------------------------------------------------------------------
--  nT    : coefficients of signatures  <agg> <size> <length>
--  nT    : "remainders"                <agg>
--  nT    : "quotients"                 <agg>
--  14nT  : bitstring                   <size>
--  nT    : square of coeffs of sigs    <length>
--  T     : sum(squares) % Q            <length>

-- | Generate inputs from `Param`
genInputFromParam :: Param a -> [a]
genInputFromParam (Param _ _ setup settings) =
  let forAggChecking =
        if enableAggChecking settings
          then
            (setupSignatures setup >>= elems)
              ++ (setupSigRemainders setup >>= elems)
              ++ (setupSigQuotients setup >>= elems)
          else []

      forSizeChecking =
        if enableSizeChecking settings
          then concat (concat (setupSigBitStrings setup))
          else []

      forLengthChecking =
        if enableLengthChecking settings
          then sigSquares <> sigLengths
          else []
      sigSquares = concatMap elems (setupSigSquares setup)
      sigLengths = setupSigLengths setup
   in forAggChecking
        ++ forSizeChecking
        ++ forLengthChecking

--------------------------------------------------------------------------------

-- split a list into Arrays each of length n
splitListIntoArrays :: Int -> [a] -> [Array Int a]
splitListIntoArrays _ [] = mempty
splitListIntoArrays n list = listArray (0, n - 1) first : splitListIntoArrays n rest
  where
    (first, rest) = splitAt n list

--------------------------------------------------------------------------------

-- shiftPublicKeyBy i xs = xs ^ i mod xⁿ + 1
-- OBSERVATION:
-- suppose the public key is a polynomial:

--   a  + bx  + cx² + ... + dx⁽ⁿ ⁻ ²⁾ + ex⁽ⁿ ⁻ ¹⁾

-- if we times it by x:

--   ax + bx² + cx³ + ... + dx⁽ⁿ ⁻ ¹⁾ + exⁿ

-- and then mod it by (xⁿ + 1), the resulting polynomial should look like this:

--   -e + ax + bx² + cx³ + ... dx⁽ⁿ ⁻ ¹⁾

-- if the public key is a polynomial made up of this array of coefficients:

--   [a, b, c, ..., d, e]

-- we should rotate the array to right by 1 and then make the wrapped coefficients negative:

--   [-e, a, b, c, ..., d]

shiftPublicKeyBy :: GaloisField a => Int -> Int -> PublicKey a -> PublicKey a
shiftPublicKeyBy dimension i xs =
  let (withInBound, outOfBound) = splitAt (dimension - i) (elems xs)
      wrapped = map negate outOfBound
   in listArray (0, dimension - 1) $ wrapped ++ withInBound
