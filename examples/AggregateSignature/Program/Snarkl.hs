{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use if" #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module AggregateSignature.Program.Snarkl where

import AggregateSignature.Util
import Snarkl


-- ensure that a signature is smaller than 16384 (target: 12289)
checkSignaturesBitString :: (Integral a, GaloisField a) => Int -> [Signature a] -> TExp ('TArr ('TArr ('TArr 'TField))) a -> Comp 'TBool a
checkSignaturesBitString dimension signatures bitStringss = everyM [0 .. length signatures - 1] checkSignature
  where
    checkSignature i = do
      let signature = signatures !! i
      everyM [0 .. dimension - 1] (checkSignatureTerm signature i)

    checkSignatureTerm signature i j = do
      let term = signature !! j
      total <- reduce 0 [0 .. 13] $ \accum k -> do
        bit <- access3 bitStringss (i, j, k)
        let bitValue = fromIntegral (2 ^ k :: Integer)
        let prod = bit * bitValue
        return (accum + prod)

      return (fromIntegral term `eq` total)

-- ensure that a signature's bitstring is really made of bits (either 1 or 0)
checkSignaturesBits :: (Integral a, GaloisField a) => Int -> Int -> TExp ('TArr ('TArr ('TArr 'TField))) a -> Comp 'TBool a
checkSignaturesBits numberOfSignatures dimension bitStringss =
  everyM
    [0 .. numberOfSignatures - 1]
    (\i -> everyM [0 .. dimension - 1] (everyM [0 .. 13] . either1or0 i))
  where
    either1or0 i j k = do
      bit <- access3 bitStringss (i, j, k)
      return $ (bit * bit) `eq` bit

computeAggregateSignature :: (Integral a, GaloisField a) => PublicKey a -> [Signature a] -> Comp ('TArr 'TField) a
computeAggregateSignature publicKey signatures = do
  let dimension = length publicKey
  -- actual calculated aggregate signature are stored here
  actualAggSig <- createArray dimension

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

checkSquares :: (Integral a, GaloisField a) => Int -> Int -> [Signature a] -> TExp ('TArr ('TArr 'TField)) a -> Comp 'TBool a
checkSquares numberOfSignatures dimension signatures sigSquares = do
  -- for each signature
  everyM [0 .. numberOfSignatures - 1] $ \i -> do
    let signature = signatures !! i
    -- for each term of signature
    everyM [0 .. dimension - 1] $ \j -> do
      let term = fromIntegral (signature !! j)
      square <- access2 sigSquares (i, j)
      return (square `eq` (term * term))

checkLength :: (Integral a, GaloisField a) => Int -> Int -> TExp ('TArr ('TArr 'TField)) a -> TExp ('TArr 'TField) a -> Comp 'TBool a
checkLength numberOfSignatures dimension sigSquares sigLengths = do
  -- for each signature
  everyM [0 .. numberOfSignatures - 1] $ \i -> do
    expectedLength <- access sigLengths i
    -- for each term of signature
    actualLength <- reduce 0 [0 .. dimension - 1] $ \accum j -> do
      square <- access2 sigSquares (i, j)
      return (accum + square)

    return (expectedLength `eq` actualLength)

  -- { enableAggSigChecking :: Bool,
  --   enableBitStringSizeChecking :: Bool,
  --   enableBitStringValueChecking :: Bool,
  --   enableSigSquareChecking :: Bool,
  --   enableSigLengthChecking :: Bool
aggregateSignature :: (Integral a, GaloisField a) => Setup a -> Comp 'TBool a
aggregateSignature (Setup dimension n publicKey signatures _ settings) = do
  -- check aggregate signature
  aggSigOk <- case enableAggSigChecking settings of
    False -> return true
    True -> do
      -- expected computed aggregate signature as input
      expectedAggSig <- createArrayFromInput dimension :: Comp ('TArr 'TField) a

      actualAggSig <- computeAggregateSignature publicKey signatures
      arrayEq dimension expectedAggSig actualAggSig

  -- expected bitstring of signatures as input
  sigBitStrings <- case enableBitStringSizeChecking settings || enableBitStringValueChecking settings of
    False -> freshInputs3 0 0 0 :: Show a => Comp ('TArr ('TArr ('TArr 'TField))) a
    True -> freshInputs3 n dimension 14 :: Show a => Comp ('TArr ('TArr ('TArr 'TField))) a

  -- check signature size
  sigSizeOk <- case enableBitStringSizeChecking settings of
    False -> return true
    True -> checkSignaturesBitString dimension signatures sigBitStrings

  -- check signature bits
  sigBitsOk <- case enableBitStringValueChecking settings of
    False -> return true
    True -> checkSignaturesBits n dimension sigBitStrings

  -- expected squares of signatures as input
  sigSquares <- case enableSigSquareChecking settings || enableSigLengthChecking settings of
    False -> freshInputs2 0 0 :: Show a => Comp ('TArr ('TArr 'TField)) a
    True -> freshInputs2 n dimension :: Show a => Comp ('TArr ('TArr 'TField)) a

  -- check squares of signatures
  sigSquaresOk <- case enableSigSquareChecking settings of
    False -> return true
    True -> do
      checkSquares n dimension signatures sigSquares

  -- check length of signatures
  sigLengthsOk <- case enableSigLengthChecking settings of
    False -> return true
    True -> do
      -- expected length of signatures as input
      sigLengths <- createArrayFromInput n :: Show a => Comp ('TArr 'TField) a
      checkLength n dimension sigSquares sigLengths

  every id [aggSigOk, sigSizeOk, sigBitsOk, sigSquaresOk, sigLengthsOk]