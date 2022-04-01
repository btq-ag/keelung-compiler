{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use if" #-}


module AggregateSignature.Program.Keelung where

import AggregateSignature.Util
import Keelung
import Data.Array

-- ensure that a signature is smaller than 16384 (target: 12289)
checkSignaturesBitStringSize :: (GaloisField n, Integral n) => Int -> [Signature n] -> Ref ('A ('A ('A ('V 'Bool)))) -> Comp 'Bool n 
checkSignaturesBitStringSize dimension signatures bitStringss =
  everyM [0 .. length signatures - 1] checkSignature
  where
    checkSignature i = do
      let signature = signatures !! i
      everyM [0 .. dimension - 1] (checkSignatureTerm signature i)

    checkSignatureTerm signature i j = do
      let term = signature ! j
      total <- reduce 0 [0 .. 13] $ \acc k -> do
        bit <- access3 bitStringss (i, j, k)
        let bitValue = fromIntegral (2 ^ k :: Integer)
        let prod = fromBool (Var bit) * bitValue
        return (acc + prod)
      return (fromIntegral term `Eq` total)

-- ensure that a signature's bitstring is really made of bits (either 1 or 0)
checkSignaturesBits :: GaloisField n => Int -> Int -> Ref ('A ('A ('A ('V 'Bool)))) -> Comp 'Bool n 
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

checkSquares :: (GaloisField n, Integral n) => Int -> Int -> [Signature n] -> Ref ('A ('A ('V 'Num))) -> Comp 'Bool n 
checkSquares numberOfSignatures dimension signatures sigSquares = do
  -- for each signature
  everyM [0 .. numberOfSignatures - 1] $ \i -> do
    let signature = signatures !! i
    -- for each term of signature
    everyM [0 .. dimension - 1] $ \j -> do
      let term = fromIntegral (signature ! j)
      square <- access2 sigSquares (i, j)
      return (Var square `Eq` (term * term))

checkLength :: (Integral n, GaloisField n) => Int -> Int -> Ref ('A ('A ('V 'Num))) -> Ref ('A ('V 'Num)) -> Comp 'Bool n 
checkLength numberOfSignatures dimension sigSquares sigLengths = do
  -- for each signature
  everyM [0 .. numberOfSignatures - 1] $ \i -> do
    expectedLength <- access sigLengths i
    -- for each term of signature
    actualLength <- reduce 0 [0 .. dimension - 1] $ \acc j -> do
      square <- access2 sigSquares (i, j)
      return (acc + Var square)

    return (Var expectedLength `Eq` actualLength)

aggregateSignature :: (Integral n, GaloisField n) => Setup n -> Comp 'Bool n 
aggregateSignature (Setup dimension n publicKey signatures _ settings) = do
  -- check aggregate signature
  aggSigOk <- case enableAggSigChecking settings of
    False -> return true
    True -> do
      -- expected computed aggregate signature as input
      expectedAggSig <- freshInputs dimension

      actualAggSig <- computeAggregateSignature publicKey signatures
      arrayEq dimension expectedAggSig actualAggSig

  -- check signature size
  sigSizeOk <- case enableSigSizeChecking settings of
    False -> return true
    True -> do 
      sigBitStrings <- freshInputs3 n dimension 14
      checkSignaturesBitStringSize dimension signatures sigBitStrings

  -- check squares & length of signatures
  sigSquaresAndLengthsOk <- case enableSigLengthChecking settings of
    False -> return true 
    True -> do 
      sigSquares <- freshInputs2 n dimension
      squareOk <- checkSquares n dimension signatures sigSquares
      -- expected length of signatures as input
      sigLengths <- freshInputs n
      lengthOk <- checkLength n dimension sigSquares sigLengths

      return (squareOk `And` lengthOk)

  every id [aggSigOk, sigSizeOk, sigSquaresAndLengthsOk]

