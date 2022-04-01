{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use if" #-}

module AggregateSignature.Program.Keelung where

import AggregateSignature.Util
import Data.Array
import Keelung

-- ensure that a signature's bitstring is really made of bits (either 1 or 0)
-- checkSignaturesBits :: GaloisField n => Int -> Int -> Ref ('A ('A ('A ('V 'Bool)))) -> Comp 'Bool n
-- checkSignaturesBits _numberOfSignatures _dimension _bitStringss = return true

-- -- everyM
-- --   [0 .. numberOfSignatures - 1]
-- --   (\i -> everyM [0 .. dimension - 1] (everyM [0 .. 13] . either1or0 i))
-- -- where
-- --   either1or0 i j k = do
-- --     bit <- fromBool . Var <$> access3 bitStringss (i, j, k)
-- --     return $ (bit * bit) `Eq` bit

checkAgg :: (Integral n, GaloisField n) => Setup n -> Comp 'Bool n
checkAgg (Setup dimension _ publicKey signatures _ _) = do
  -- expected computed aggregate signature as input
  expectedAggSig <- freshInputs dimension

  actualAggSig <- computeAggregateSignature publicKey signatures
  arrayEq dimension expectedAggSig actualAggSig

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

-- ensure that a signature has the right size (smaller than 16384 (target: 12289))
checkSize :: (GaloisField n, Integral n) => Setup n -> Comp 'Bool n
checkSize (Setup dimension numOfSigs _ signatures _ _) = do
  sigBitStrings <- freshInputs3 numOfSigs dimension 14
  everyM [0 .. length signatures - 1] $ \i -> do
    let signature = signatures !! i
    everyM [0 .. dimension - 1] $ \j -> do
      let term = signature ! j
      total <- reduce 0 [0 .. 13] $ \acc k -> do
        bit <- access3 sigBitStrings (i, j, k)
        let bitValue = fromIntegral (2 ^ k :: Integer)
        let prod = fromBool (Var bit) * bitValue
        return (acc + prod)
      return (fromIntegral term `Eq` total)

checkLength :: (Integral n, GaloisField n) => Setup n -> Comp 'Bool n
checkLength (Setup dimension numOfSigs _ signatures _ _) = do
  -- expected square of signatures as input
  sigSquares <- freshInputs2 numOfSigs dimension
  squareOk <- do
    -- for each signature
    everyM [0 .. numOfSigs - 1] $ \i -> do
      let signature = signatures !! i
      -- for each term of signature
      everyM [0 .. dimension - 1] $ \j -> do
        let term = fromIntegral (signature ! j)
        square <- access2 sigSquares (i, j)
        return (Var square `Eq` (term * term))
  -- expected length of signatures as input
  sigLengths <- freshInputs numOfSigs
  lengthOk <- do
    -- for each signature
    everyM [0 .. numOfSigs - 1] $ \i -> do
      expectedLength <- access sigLengths i
      -- for each term of signature
      actualLength <- reduce 0 [0 .. dimension - 1] $ \acc j -> do
        square <- access2 sigSquares (i, j)
        return (acc + Var square)

      return (Var expectedLength `Eq` actualLength)
  return (squareOk `And` lengthOk)

aggregateSignature :: (Integral n, GaloisField n) => Setup n -> Comp 'Bool n
aggregateSignature setup = do
  let settings = setupSettings setup
  -- check aggregate signature
  aggSigOk <- case enableAggSigChecking settings of
    False -> return true
    True -> checkAgg setup

  -- check signature size
  sigSizeOk <- case enableSigSizeChecking settings of
    False -> return true
    True -> checkSize setup

  -- check squares & length of signatures
  sigSquaresAndLengthsOk <- case enableSigLengthChecking settings of
    False -> return true
    True -> checkLength setup

  return $ aggSigOk `And` sigSizeOk `And` sigSquaresAndLengthsOk
