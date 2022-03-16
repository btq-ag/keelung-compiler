{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use if" #-}

-- {-# LANGUAGE RebindableSyntax #-}

module AggregateSignature.Program where

import AggregateSignature.Util
-- import Data.Bits (Bits (shiftL, testBit, (.|.)))
-- import qualified Data.Bool as Bool
-- import Data.Foldable (for_)
import Keelung

-- ensure that a signature is smaller than 16384 (target: 12289)
checkSignaturesBitString :: (GaloisField n, Integral n) => Int -> [Signature n] -> Ref ('A ('A ('A ('V 'Bool)))) -> Comp n 'Bool
checkSignaturesBitString dimension signatures bitStringss =
  everyM [0 .. length signatures - 1] checkSignature
  where
    checkSignature i = do
      let signature = signatures !! i
      everyM [0 .. dimension - 1] (checkSignatureTerm signature i)

    checkSignatureTerm signature i j = do
      let term = signature !! j
      total <- reduce 0 [0 .. 13] $ \accum k -> do
        bit <- access3 bitStringss (i, j, k)
        let bitValue = fromIntegral (2 ^ k :: Integer)
        let prod = fromBool (Var bit) * bitValue
        return (accum + prod)
      return (fromIntegral term `Eq` total)

-- ensure that a signature's bitstring is really made of bits (either 1 or 0)
checkSignaturesBits :: GaloisField n => Int -> Int -> Ref ('A ('A ('A ('V 'Bool)))) -> Comp n 'Bool
checkSignaturesBits _numberOfSignatures _dimension _bitStringss = return true

-- everyM
--   [0 .. numberOfSignatures - 1]
--   (\i -> everyM [0 .. dimension - 1] (everyM [0 .. 13] . either1or0 i))
-- where
--   either1or0 i j k = do
--     bit <- fromBool . Var <$> access3 bitStringss (i, j, k)
--     return $ (bit * bit) `Eq` bit

computeAggregateSignature :: (Integral n, GaloisField n) => PublicKey n -> [Signature n] -> M n (Ref ('A ('V 'Num)))
computeAggregateSignature publicKey signatures = do
  let dimension = length publicKey
  -- actual calculated aggregate signature are stored here
  actualAggSig <- allocate dimension

  -- for shifting the public key
  loop [0 .. dimension - 1] $ \i -> do
    let shiftedPublicKey = shiftPublicKeyBy i publicKey
    -- for each signature
    total <- reduce 0 signatures $ \accum signature -> do
      reduce accum [0 .. dimension - 1] $ \accum' k -> do
        let pk = shiftedPublicKey !! k
        let sig = signature !! k
        let prod = pk * sig
        return (accum' + fromIntegral prod)

    update actualAggSig i total

  return actualAggSig

checkSquares :: (GaloisField n, Integral n) => Int -> Int -> [Signature n] -> Ref ('A ('A ('V 'Num))) -> Comp n 'Bool
checkSquares numberOfSignatures dimension signatures sigSquares = do
  -- for each signature
  everyM [0 .. numberOfSignatures - 1] $ \i -> do
    let signature = signatures !! i
    -- for each term of signature
    everyM [0 .. dimension - 1] $ \j -> do
      let term = fromIntegral (signature !! j)
      square <- access2 sigSquares (i, j)
      return (Var square `Eq` (term * term))

checkLength :: (Integral n, GaloisField n) => Int -> Int -> Ref ('A ('A ('V 'Num))) -> Ref ('A ('V 'Num)) -> Comp n 'Bool
checkLength numberOfSignatures dimension sigSquares sigLengths = do
  -- for each signature
  everyM [0 .. numberOfSignatures - 1] $ \i -> do
    expectedLength <- access sigLengths i
    -- for each term of signature
    actualLength <- reduce 0 [0 .. dimension - 1] $ \accum j -> do
      square <- access2 sigSquares (i, j)
      return (accum + Var square)

    return (Var expectedLength `Eq` actualLength)

aggregateSignature :: (Integral n, GaloisField n) => Setup n -> Comp n 'Bool
aggregateSignature (Setup dimension n publicKey signatures _ settings) = do
  -- check aggregate signature
  aggSigOk <- case enableAggSigChecking settings of
    False -> return true
    True -> do
      -- expected computed aggregate signature as input
      expectedAggSig <- freshInputs dimension

      actualAggSig <- computeAggregateSignature publicKey signatures
      arrayEq dimension expectedAggSig actualAggSig

  -- expected bitstring of signatures as input
  sigBitStrings <- case enableBitStringChecking settings || enableSigSquareChecking settings of
    False -> freshInputs3 0 0 0 
    True -> freshInputs3 n dimension 14

  -- check signature size
  sigSizeOk <- case enableBitStringChecking settings of
    False -> return true
    True -> checkSignaturesBitString dimension signatures sigBitStrings

  -- check signature bits
  sigBitsOk <- case enableSigSquareChecking settings of
    False -> return true
    True -> checkSignaturesBits n dimension sigBitStrings

  -- expected squares of signatures as input
  sigSquares <- case enableSigSquareChecking settings || enableSigSquareChecking settings of
    False -> freshInputs2 0 0
    True -> freshInputs2 n dimension

  -- check squares of signatures
  sigSquaresOk <- case enableSigSquareChecking settings of
    False -> return true
    True -> do
      checkSquares n dimension signatures sigSquares

  -- check length of signatures
  sigLengthsOk <- case enableSigSquareChecking settings of
    False -> return true
    True -> do
      -- expected length of signatures as input
      sigLengths <- freshInputs n
      checkLength n dimension sigSquares sigLengths

  every id [aggSigOk, sigSizeOk, sigBitsOk, sigSquaresOk, sigLengthsOk]
