module AggregateSignature.Util where

import Data.Array
import Data.Bits (testBit)
import Data.Field.Galois (GaloisField)
import Data.Semiring (Semiring (..))
import System.Random

--------------------------------------------------------------------------------

type Signature n = Array Int n

type PublicKey n = Array Int n

--------------------------------------------------------------------------------

-- | Settings for Aggregate Signature
data Setup n = Setup
  { setupDimension :: Int,
    setupNumberOfSignatures :: Int,
    setupPublicKey :: PublicKey n,
    setupSignatures :: [Signature n],
    setupInputs :: Input n,
    setupSettings :: Settings
  }

--------------------------------------------------------------------------------

q :: (Integral n, Num n) => n 
q = 12289

-- | Inputs for the system
data Input a = Input
  { -- | Signatures to be aggregated
    inputSignatures :: [Signature a],
    -- | "Remainders"
    inputSigRemainders :: [Array Int a],
    -- | "Quotients"
    inputSigQuotients :: [Array Int a],
    -- | Aggregate signature
    inputAggSigs :: Signature a,
    -- | Bit strings of signatures
    inputSigBitStrings :: [[[a]]],
    -- | Squares of coefficients of signatures
    inputSigSquares :: [Signature a],
    -- | Sume of squares of coefficients signatures
    inputSigLengths :: [a]
  }

-- | Settings for enabling/disabling different part of Aggregate Signature
data Settings = Settings
  { enableAggSigChecking :: Bool,
    enableSigSizeChecking :: Bool,
    enableSigLengthChecking :: Bool
  }

--------------------------------------------------------------------------------

makeSetup :: (Random n, GaloisField n, Integral n, Num n) => Int -> Int -> Int -> Settings -> Setup n
makeSetup dimension t seed settings =
  Setup
    { setupDimension = dimension,
      setupNumberOfSignatures = t,
      setupPublicKey = publicKey,
      setupSignatures = signatures,
      setupInputs = Input signatures remainders quotients aggSigs bisStrings sigSquares sigLengths,
      setupSettings = settings
    }
  where
    -- raw input numbers range from of `-q/2` to `q/2`
    -- this function move the negative numbers from [ -q/2 , 0 ) to [ q/2 , q ) by adding `q`
    -- rectify :: (Integral n, Num n, Eq n) => n -> n
    -- rectify n = if signum n == -1 then n + q else n

    -- domain of coefficients of signatures: [0, 12289)
    signatures :: Num n => [Signature n]
    signatures = map (fmap (fromIntegral . (`mod` 12289))) arraysForSignatures

    -- domain of terms of public keys: [0, 2^181)
    publicKeys :: Num n => [PublicKey n]
    publicKeys = map (fmap fromIntegral) arraysForPublicKeys

    (remainders, quotients) = unzip $ zipWith (calculate dimension) signatures publicKeys

    -- NOTE: somehow generating new `StdGen` from IO would result in segmentation fault (possibly due to FFI)
    publicKey = listArray (0, dimension - 1) $ take dimension $ randoms (mkStdGen seed)

    -- generate fake numbers for populating fake signatures & public keys
    randomNumbers :: [Int]
    randomNumbers = take (dimension * t * 2) $ randoms (mkStdGen (succ seed))

    -- split random numbers into small arrays (of size `dimension`) for fake signatures & public keys
    arraysForSignatures :: [Array Int Int]
    arraysForPublicKeys :: [Array Int Int]
    (arraysForSignatures, arraysForPublicKeys) = splitAt t $ splitListIntoArrays dimension randomNumbers

    aggSigs = listArray (0, dimension - 1) $ map ithSum [0 .. dimension - 1]
      where
        ithSum i =
          let shiftedPublicKey = shiftPublicKeyBy dimension i publicKey
           in sum $ map (sum . zipWith (*) (elems shiftedPublicKey) . elems) signatures

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
--        ┌──────────────────────────  ...  ────────────────────┐
--    i   │                                                     │
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
--        └─────────────────────────── ... ─────────────────────┘

-- Get an array of remainders and an array of quotients from a signature and a public key 
calculate :: (Integral n, Num n) => Int -> Signature n -> PublicKey n -> (Array Int n, Array Int n)
calculate dimension signature publicKey =
  let (remainders, quotients) = unzip [handleRow i | i <- [0 .. dimension]]
   in (listArray (0, dimension - 1) remainders, listArray (0, dimension - 1) quotients)
  where

    handleRow i =
      let total = sum [lookupSigPk i j | j <- [0 .. dimension]]
       in (total `mod` q, total `div` q)

    lookupSigPk i j =
      signature ! j
        * ( if i < j
              then q - (publicKey ! (dimension + i - j))
              else publicKey ! (i - j)
          )

--------------------------------------------------------------------------------

-- | Generate inputs from a Setup
genInputFromSetup :: Setup a -> [a]
genInputFromSetup (Setup _ _ _ _ inputs settings) =
  let aggSigs = inputAggSigs inputs -- 512 terms x 512
      bitStrings = concat (concat (inputSigBitStrings inputs))
      sigSquares = concatMap elems (inputSigSquares inputs)
      sigLengths = inputSigLengths inputs
   in ( if enableAggSigChecking settings
          then elems aggSigs
          else []
      )
        <> ( if enableSigSizeChecking settings
               then bitStrings
               else []
           )
        <> ( if enableSigLengthChecking settings then sigSquares <> sigLengths else []
           )

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
