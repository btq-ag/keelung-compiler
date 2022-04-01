{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use if" #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module AggregateSignature.Program.Snarkl where

import AggregateSignature.Util
import Data.Array
import Snarkl

computeAggregateSignature :: (Integral a, GaloisField a) => PublicKey a -> [Signature a] -> Comp ('TArr 'TField) a
computeAggregateSignature publicKey signatures = do
  let dimension = length publicKey
  -- actual calculated aggregate signature are stored here
  actualAggSig <- createArray dimension

  -- for shifting the public key
  loop [0 .. dimension - 1] $ \i -> do
    let shiftedPublicKey = shiftPublicKeyBy dimension i publicKey
    -- for each signature
    total <- reduce 0 signatures $ \acc signature -> do
      reduce acc [0 .. dimension - 1] $ \acc' k -> do
        let pk = shiftedPublicKey ! k
        let sig = signature ! k
        let prod = pk * sig
        return (acc' + fromIntegral prod)

    update actualAggSig i total

  return actualAggSig

checkLength :: (Integral a, GaloisField a) => Setup a -> Comp 'TBool a
checkLength (Setup dimension numOfSigs _ signatures _ _) = do
  -- expected square of signatures as input
  sigSquares <- freshInputs2 numOfSigs dimension :: Show a => Comp ('TArr ('TArr 'TField)) a
  squareOk <- do
    -- for each signature
    everyM [0 .. numOfSigs - 1] $ \i -> do
      let signature = signatures !! i
      -- for each term of signature
      everyM [0 .. dimension - 1] $ \j -> do
        let term = fromIntegral (signature ! j)
        square <- access2 sigSquares (i, j)
        return (square `eq` (term * term))

  -- expected length of signatures as input
  sigLengths <- createArrayFromInput numOfSigs :: Show a => Comp ('TArr 'TField) a
  lengthOk <- do
    -- for each signature
    everyM [0 .. numOfSigs - 1] $ \i -> do
      expectedLength <- access sigLengths i
      -- for each term of signature
      actualLength <- reduce 0 [0 .. dimension - 1] $ \acc j -> do
        square <- access2 sigSquares (i, j)
        return (acc + square)

      return (expectedLength `eq` actualLength)

  return $ squareOk && lengthOk

checkAgg :: (Integral a, GaloisField a) => Setup a -> Comp 'TBool a
checkAgg (Setup dimension _ publicKey signatures _ _) = do
  -- expected computed aggregate signature as input
  expectedAggSig <- createArrayFromInput dimension :: Comp ('TArr 'TField) a
  actualAggSig <- computeAggregateSignature publicKey signatures
  arrayEq dimension expectedAggSig actualAggSig

checkSize :: (Integral a, GaloisField a) => Setup a -> Comp 'TBool a
checkSize (Setup dimension numOfSigs _ signatures _ _) = do
  sigBitStrings <- freshInputs3 numOfSigs dimension 14 :: Show a => Comp ('TArr ('TArr ('TArr 'TField))) a
  sigBitsOk <- checkSignaturesBits sigBitStrings
  sigSizeOk <- checkSignaturesBitString sigBitStrings
  return $ sigBitsOk && sigSizeOk
  where
    -- ensure that a signature is smaller than 16384 (target: 12289)
    checkSignaturesBitString :: (Integral a, GaloisField a) => TExp ('TArr ('TArr ('TArr 'TField))) a -> Comp 'TBool a
    checkSignaturesBitString bitStringss = everyM [0 .. length signatures - 1] checkSignature
      where
        checkSignature i = do
          let signature = signatures !! i
          everyM [0 .. dimension - 1] (checkSignatureTerm signature i)

        checkSignatureTerm signature i j = do
          let term = signature ! j
          total <- reduce 0 [0 .. 13] $ \acc k -> do
            bit <- access3 bitStringss (i, j, k)
            let bitValue = fromIntegral (2 ^ k :: Integer)
            let prod = bit * bitValue
            return (acc + prod)

          return (fromIntegral term `eq` total)

    -- ensure that a signature's bitstring is really made of bits (either 1 or 0)
    checkSignaturesBits :: (Integral a, GaloisField a) => TExp ('TArr ('TArr ('TArr 'TField))) a -> Comp 'TBool a
    checkSignaturesBits bitStringss =
      everyM
        [0 .. numOfSigs - 1]
        (\i -> everyM [0 .. dimension - 1] (everyM [0 .. 13] . either1or0 i))
      where
        either1or0 i j k = do
          bit <- access3 bitStringss (i, j, k)
          return $ (bit * bit) `eq` bit

aggregateSignature :: (Integral a, GaloisField a) => Setup a -> Comp 'TBool a
aggregateSignature setup = do
  let settings = setupSettings setup
  -- check aggregate signature
  aggOk <- case enableAggSigChecking settings of
    False -> return true
    True -> checkAgg setup

  -- expected bitstring of signatures as input
  squareOk <- case enableSigSizeChecking settings of
    False -> return true
    True -> checkSize setup

  -- expected squares of signatures as input
  lengthOk <- case enableSigLengthChecking settings of
    False -> return true
    True -> checkLength setup

  return $ aggOk && squareOk && lengthOk