module AggregateSignature.Util where

import Data.Bits (testBit)
import Data.Field.Galois (GaloisField)
import Data.Semiring (Semiring (..))
import System.Random

--------------------------------------------------------------------------------

type Signature a = [a]

type PublicKey a = [a]

--------------------------------------------------------------------------------

-- | Settings for Aggregate Signature
data Setup a = Setup
  { setupDimension :: Int,
    setupNumberOfSignatures :: Int,
    setupPublicKey :: PublicKey a,
    setupSignatures :: [Signature a],
    setupInputs :: Input a,
    setupSettings :: Settings
  }

--------------------------------------------------------------------------------

-- | Inputs for the system
data Input a = Input
  { inputAggSigs :: [a],
    inputSigBitStrings :: [[[a]]],
    inputSigSquares :: [[a]],
    inputSigLengths :: [a]
  }

-- | Settings for enabling/disabling different part of Aggregate Signature
data Settings = Settings
  { enableAggSigChecking :: Bool,
    enableSigSizeChecking :: Bool,
    enableSigLengthChecking :: Bool
  }

--------------------------------------------------------------------------------

makeSetup :: (Random a, GaloisField a, Integral a, Num a) => Int -> Int -> Int -> Settings -> Setup a
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
    publicKey = take dimension $ randoms (mkStdGen seed)

    genInts :: Int -> [Int]
    genInts amount = take amount $ randoms (mkStdGen (succ seed))

    signatures = splitEvery dimension $ map (\i -> fromIntegral (i `mod` 12289)) $ genInts (dimension * t)

    aggSigs = map ithSum [0 .. dimension - 1]
      where
        ithSum i =
          let shiftedPublicKey = shiftPublicKeyBy i publicKey
           in sum $ map (sum . zipWith (*) shiftedPublicKey) signatures

    bisStrings = map toBitStrings signatures
    toBitStrings = map (toListLE . toInteger)

    {-# INLINE toListLE #-}
    toListLE :: GaloisField a => Integer -> [a]
    toListLE b = fmap (toGF . testBit b) [0 .. 13]

    toGF :: GaloisField a => Bool -> a
    toGF True = one
    toGF False = zero

    sigSquares = map (map (\x -> x * x)) signatures

    sigLengths = map sum sigSquares

--------------------------------------------------------------------------------

-- | Generate inputs from a Setup
genInputFromSetup :: Setup a -> [a]
genInputFromSetup (Setup _ _ _ _ inputs settings) =
  let aggSigs = inputAggSigs inputs
      bitStrings = concat (concat (inputSigBitStrings inputs))
      sigSquares = concat (inputSigSquares inputs)
      sigLengths = inputSigLengths inputs
   in ( if enableAggSigChecking settings
          then aggSigs
          else []
      )
        <> ( if enableSigSizeChecking settings
               then bitStrings
               else []
           )
        <> ( if enableSigLengthChecking settings then sigSquares <> sigLengths else []
           )

--------------------------------------------------------------------------------

splitEvery :: Int -> [a] -> [[a]]
splitEvery _ [] = []
splitEvery n list = first : splitEvery n rest
  where
    (first, rest) = splitAt n list

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

shiftPublicKeyBy :: GaloisField a => Int -> PublicKey a -> PublicKey a
shiftPublicKeyBy i xs =
  let (withInBound, outOfBound) = splitAt (length xs - i) xs
      wrapped = map negate outOfBound
   in wrapped ++ withInBound
