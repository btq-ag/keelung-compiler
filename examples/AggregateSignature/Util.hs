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

    signatures :: Num n => [Signature n]
    signatures = splitEvery dimension $ map (fromIntegral . (`mod` 12289)) $ genInts (dimension * t)

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
  let aggSigs = inputAggSigs inputs
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

splitEvery :: Int -> [a] -> [Signature a]
splitEvery _ [] = mempty
splitEvery n list = listArray (0, n - 1) first : splitEvery n rest
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

shiftPublicKeyBy :: GaloisField a => Int -> Int -> PublicKey a -> PublicKey a
shiftPublicKeyBy dimension i xs =
  let (withInBound, outOfBound) = splitAt (dimension - i) (elems xs)
      wrapped = map negate outOfBound
   in listArray (0, dimension - 1) $ wrapped ++ withInBound
