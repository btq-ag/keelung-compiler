{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use if" #-}

module AggregateSignature.Program where

import AggregateSignature.Util
import Data.Array
import Keelung
import Control.Monad

-- ensure that a signature's bitstring is really made of bits (either 1 or 0)
-- checkSignaturesBits :: GaloisField n => Int -> Int -> Ref ('A ('A ('A ('V 'Bool)))) -> Comp n (Expr 'Bool n)
-- checkSignaturesBits _numberOfSignatures _dimension _bitStringss = return true

-- -- everyM
-- --   [0 .. numberOfSignatures - 1]
-- --   (\i -> everyM [0 .. dimension - 1] (everyM [0 .. 13] . either1or0 i))
-- -- where
-- --   either1or0 i j k = do
-- --     bit <- fromBool . Var <$> access3 bitStringss (i, j, k)
-- --     return $ (bit * bit) `Eq` bit

checkAgg :: (Integral n, GaloisField n) => Setup n -> Comp n ()
checkAgg (Setup dimension _ publicKey signatures _ _) = do
  -- expected computed aggregate signature as input
  expectedAggSig <- freshInputs dimension

  actualAggSig <- computeAggregateSignature publicKey signatures
  arrayEq dimension expectedAggSig actualAggSig

computeAggregateSignature :: (Integral n, GaloisField n) => PublicKey n -> [Signature n] -> Comp n (Ref ('A ('V 'Num)))
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

-- ensure that the coefficients of signatures are in the range of [0, 12289)
-- representing the coefficients with bitstrings of length 14 
-- would put them in the range of [0, 16384)
-- since 12288 is 3/4 of 16384, we can use the highest 2 bits to check
-- if the coefficients are in the right quarters 
-- 
-- the highest 2 bits (bitstring[13, 12]): 
--      00 -> within range 
--      01 -> within range 
--      10 -> within range 
--      11 -> within range only when the remaining bits are 0s
--
-- the coefficients will only be in the range of [0, 12289) if and only if:
--      bitstring[13] * bitstring[12] * (sum of bitstring[11 .. 0]) = 0

checkSize :: (GaloisField n, Integral n) => Setup n -> Comp n ()
checkSize (Setup dimension numOfSigs _ signatures _ _) = do
  sigBitStrings <- freshInputs3 numOfSigs dimension 14
  forM_ [0 .. length signatures - 1] $ \i -> do
    let signature = signatures !! i
    forM_ [0 .. dimension - 1] $ \j -> do
      let coeff = signature ! j

      -- within the range of [0, 16384)
      value <- reduce 0 [0 .. 13] $ \acc k -> do
        bit <- access3 sigBitStrings (i, j, k)
        let bitValue = fromIntegral (2 ^ k :: Integer)
        let prod = fromBool (Var bit) * bitValue
        return (acc + prod)
      assert (fromIntegral coeff `Eq` value)

      bit13 <- access3 sigBitStrings (i, j, 13)
      bit12 <- access3 sigBitStrings (i, j, 12)
      bit11to0 <- reduce 0 [0 .. 11] $ \acc k -> do
        bit <- access3 sigBitStrings (i, j, k)
        return (acc + fromBool (Var bit))

      let smallerThan12289 = fromBool (Var bit13) * fromBool (Var bit12) * bit11to0
      assert (smallerThan12289 `Eq` 0)
      
checkLength :: (Integral n, GaloisField n) => Setup n -> Comp n ()
checkLength (Setup dimension numOfSigs _ signatures _ _) = do
  -- expected square of signatures as input
  sigSquares <- freshInputs2 numOfSigs dimension
  -- for each signature
  forM_ [0 .. numOfSigs - 1] $ \i -> do
    let signature = signatures !! i
    -- for each term of signature
    forM_ [0 .. dimension - 1] $ \j -> do
      let term = fromIntegral (signature ! j)
      square <- access2 sigSquares (i, j)
      assert (Var square `Eq` (term * term))

  -- expected length of signatures as input
  sigLengths <- freshInputs numOfSigs

  -- for each signature
  forM_ [0 .. numOfSigs - 1] $ \i -> do
    expectedLength <- access sigLengths i
    -- for each term of signature
    actualLength <- reduce 0 [0 .. dimension - 1] $ \acc j -> do
      square <- access2 sigSquares (i, j)
      return (acc + Var square)

    assert (Var expectedLength `Eq` actualLength)

aggregateSignature :: (Integral n, GaloisField n) => Setup n -> Comp n ()
aggregateSignature setup = do
  let settings = setupSettings setup
  -- check aggregate signature
  case enableAggSigChecking settings of
    False -> return ()
    True -> checkAgg setup

  -- check signature size
  case enableSigSizeChecking settings of
    False -> return ()
    True -> checkSize setup

  -- check squares & length of signatures
  case enableSigLengthChecking settings of
    False -> return ()
    True -> checkLength setup
