{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use if" #-}

module AggregateSignature.Program where

import AggregateSignature.Util
import Control.Monad
import Data.Array
import Keelung.Compiler
import Keelung.Monad
-- import Keelung.Syntax
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

checkAgg :: (Integral n, GaloisField n) => Param n -> Comp (Val 'Unit)
checkAgg (Param dimension numOfSigs setup _) = do
  -- allocation of inputs:
  --    nT: coefficients of terms of signatures as input
  --    nT: remainders of product of signatures & public keys
  --    nT: quotients of product of signatures & public keys
  sigs <- inputs2 numOfSigs dimension
  expectedRemainders <- inputs2 numOfSigs dimension
  expectedQuotients <- inputs2 numOfSigs dimension

  -- pairs for iterating through public keys with indices
  let publicKeyPairs = zip [0 ..] (setupPublicKeys setup)

  forM_ publicKeyPairs $ \(t, publicKey) -> do
    forM_ [0 .. dimension - 1] $ \i -> do
      rowSum <- reduce 0 [0 .. dimension - 1] $ \acc j -> do
        let indexForPublicKey = (i - j) `mod` dimension
        let pk = publicKey ! indexForPublicKey
        let pk' =
              if i < j
                then q - pk
                else pk
        let sig = access2 sigs (t, j)
        return $ acc + (sig * fromIntegral pk')
      let remainder = access2 expectedRemainders (t, i)
      let quotient = access2 expectedQuotients (t, i)

      -- assert the relation between rowSum, remainder and quotient
      assert $ rowSum `Eq` (quotient * fromInteger q + remainder)

  forM_ [0 .. dimension - 1] $ \i -> do
    let expected = setupAggSig setup ! i
    let actual = foldl (\acc t -> 
                  let remainder = access2 expectedRemainders (t, i)
                  in  acc + remainder) 0 [0 .. numOfSigs - 1] 

    -- assert that the sum of remainders forms a term of aggregate signature
    assert $ actual `Eq` fromIntegral expected

  return unit

checkSize :: (GaloisField n, Integral n) => Param n -> Comp (Val 'Unit)
checkSize (Param dimension numOfSigs setup _) = do
  let signatures = setupSignatures setup

  sigBitStrings <- inputs3 numOfSigs dimension 14
  forM_ [0 .. numOfSigs - 1] $ \i -> do
    let signature = signatures !! i
    forM_ [0 .. dimension - 1] $ \j -> do
      let coeff = signature ! j

      -- within the range of [0, 16384)
      let value = foldl (\acc k ->
                            let bit = access3 sigBitStrings (i, j, k)
                                bitValue = fromIntegral (2 ^ k :: Integer)
                                prod = fromBool bit * bitValue
                            in  (acc + prod))  0 [0 .. 13]
      assert (fromIntegral coeff `Eq` value)

      let bit13 = access3 sigBitStrings (i, j, 13)
      let bit12 = access3 sigBitStrings (i, j, 12)
      let bit11to0 = foldl (\acc k ->
                              let bit = access3 sigBitStrings (i, j, k)
                              in  acc + fromBool bit) 0 [0 .. 11]

      let smallerThan12289 = fromBool bit13 * fromBool bit12 * bit11to0
      assert (smallerThan12289 `Eq` 0)

  return unit

checkLength :: (Integral n, GaloisField n) => Param n -> Comp (Val 'Unit)
checkLength (Param dimension numOfSigs _ _) = do
  sigs <- inputs2 numOfSigs dimension

  -- expecting square of signatures as input
  sigSquares <- inputs2 numOfSigs dimension
  -- for each signature
  forM_ [0 .. numOfSigs - 1] $ \t -> do
    -- for each term of signature
    forM_ [0 .. dimension - 1] $ \i -> do
      let sig = access2 sigs (t, i)
      let square = access2 sigSquares (t, i)
      assert (square `Eq` (sig * sig))

  -- expecting remainders of length of signatures as input
  sigLengthRemainders <- inputs numOfSigs
  -- expecting quotients of length of signatures as input
  sigLengthQuotients <- inputs numOfSigs

  -- for each signature
  forM_ [0 .. numOfSigs - 1] $ \t -> do
    -- for each term of signature
    let actualLength = foldl (\acc i -> 
                                  let square = access2 sigSquares (t, i)
                                  in acc + square) 0 [0 .. dimension - 1] 

    let remainder = access sigLengthRemainders t
    let quotient = access sigLengthQuotients t

    -- assert the relation between actualLength, remainder and quotient
    assert $ actualLength `Eq` (quotient * fromInteger q + remainder)

  return unit

aggregateSignature :: (Integral n, GaloisField n) => Param n -> Comp (Val 'Unit)
aggregateSignature param = do
  let settings = paramSettings param
  -- check aggregate signature
  void $ case enableAggChecking settings of
    False -> return unit
    True -> checkAgg param

  -- check signature size
  void $ case enableSizeChecking settings of
    False -> return unit
    True -> checkSize param

  -- check squares & length of signatures
  case enableLengthChecking settings of
    False -> return unit
    True -> checkLength param
