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

-- | Inputs for the system
data Input a = Input
  { inputAggSigs :: Signature a,
    inputSigBitStrings :: [[[a]]],
    inputSigSquares :: [Signature a],
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
      setupInputs = Input aggSigs bisStrings sigSquares sigLengths,
      setupSettings = settings
    }
  where
    -- NOTE: somehow generating new `StdGen` from IO would result in segmentation fault (possibly due to FFI)
    publicKey = listArray (0, dimension - 1) $ take dimension $ randoms (mkStdGen seed)

    genInts :: Int -> [Int]
    genInts amount = take amount $ randoms (mkStdGen (succ seed))

    -- generate fake numbers for populating fake signatures & public keys
    randomNumbers :: [Int]
    randomNumbers = take (dimension * t * 2) $ randoms (mkStdGen (succ seed))

    -- split random numbers into small arrays (of size `dimension`) for fake signatures & public keys
    arraysForSignatures :: [Array Int Int]
    arraysForPublicKeys :: [Array Int Int]
    (arraysForSignatures, arraysForPublicKeys) = splitAt t $ splitListIntoArrays dimension randomNumbers

    -- domain of terms of signatures: [0, 12289)
    signatures :: Num n => [Signature n]
    signatures = map (fmap (fromIntegral . (`mod` 12289))) arraysForSignatures

    -- domain of terms of public keys: [0, 2^181)
    publicKeys :: Num n => [PublicKey n]
    publicKeys = map (fmap fromIntegral) arraysForPublicKeys

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
