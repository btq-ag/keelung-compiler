{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use if" #-}

module AggregateSignature.Program where

import AggregateSignature.Util
import Control.Monad
import Data.Array
import Keelung

--    let S be the signature and P be the public key
--    let Q = q - P
--
--        j     0       1       2      ...      510     511
--    i   ┌──────────────────────────  ...  ────────────────────┐
--        │                                                     │
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
--        └──────────────────────────  ...  ────────────────────┘

checkAgg :: (Integral n, GaloisField n) => Param n -> Comp n ()
checkAgg (Param dimension numOfSigs setup _) = do
  -- allocation of inputs:
  --    nT: coefficients of terms of signatures as input
  --    nT: remainders of product of signatures & public keys
  --    nT: quotients of product of signatures & public keys
  sigs <- freshInputs2 numOfSigs dimension
  expectedRemainders <- freshInputs2 numOfSigs dimension
  expectedQuotients <- freshInputs2 numOfSigs dimension

  -- pairs for iterating through public keys with indices
  let publicKeyPairs = zip [0 ..] (setupPublicKeys setup)

  forM_ publicKeyPairs $ \(t, publicKey) -> do
    forM_ [0 .. dimension - 1] $ \i -> do
      summation <- reduce 0 [0 .. dimension - 1] $ \acc j -> do
        let indexForPublicKey = (i - j) `mod` dimension
        let pk = publicKey ! indexForPublicKey
        let pk' =
              if i < j
                then q - pk
                else pk
        sig <- access2 sigs (t, j)
        return $ acc + (Var sig * num pk')
      remainder <- access2 expectedRemainders (t, i)
      quotient <- access2 expectedQuotients (t, i)
      assert $ summation `Eq` (Var quotient * num q + Var remainder)

-- computeAggregateSignature :: (Integral n, GaloisField n) => PublicKey n -> [Signature n] -> Comp n (Ref ('A ('V 'Num)))
-- computeAggregateSignature publicKey signatures = do
--   let dimension = length publicKey
--   -- actual calculated aggregate signature are stored here
--   actualAggSig <- allocate dimension
--   -- for shifting the public key
--   loop [0 .. dimension - 1] $ \i -> do
--     let shiftedPublicKey = shiftPublicKeyBy dimension i publicKey
--     -- for each signature
--     total <- reduce 0 signatures $ \acc signature -> do
--       reduce acc [0 .. dimension - 1] $ \acc' k -> do
--         let pk = shiftedPublicKey ! k
--         let sig = signature ! k
--         let prod = pk * sig
--         return (acc' + fromIntegral prod)
--     update actualAggSig i total
--   return actualAggSig

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

checkSize :: (GaloisField n, Integral n) => Param n -> Comp n ()
checkSize (Param dimension numOfSigs setup _) = do
  let signatures = setupSignatures setup

  sigBitStrings <- freshInputs3 numOfSigs dimension 14
  forM_ [0 .. numOfSigs - 1] $ \i -> do
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

checkLength :: (Integral n, GaloisField n) => Param n -> Comp n ()
checkLength (Param dimension numOfSigs setup _) = do
  let signatures = setupSignatures setup
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

aggregateSignature :: (Integral n, GaloisField n) => Param n -> Comp n ()
aggregateSignature param = do
  let settings = paramSettings param
  -- check aggregate signature
  case enableAggChecking settings of
    False -> return ()
    True -> checkAgg param

  -- check signature size
  case enableSizeChecking settings of
    False -> return ()
    True -> checkSize param

  -- check squares & length of signatures
  case enableLengthChecking settings of
    False -> return ()
    True -> checkLength param
