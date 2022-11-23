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

checkAgg :: (Integral n, GaloisField n) => Param n -> Comp ()
checkAgg (Param dimension numOfSigs setup _) = do
  -- allocation of inputs:
  --    nT: coefficients of terms of signatures as input
  --    nT: remainders of product of signatures & public keys
  --    nT: quotients of product of signatures & public keys
  sigs <- inputs2 numOfSigs dimension :: Comp (Arr (Arr Number))
  expectedRemainders <- inputs2 numOfSigs dimension :: Comp (Arr (Arr Number))
  expectedQuotients <- inputs2 numOfSigs dimension :: Comp (Arr (Arr Number))

  -- pairs for iterating through public keys with indices
  let publicKeyPairs = zip [0 ..] (setupPublicKeys setup)

  forM_ publicKeyPairs $ \(t, publicKey) -> do
    forM_ [0 .. dimension - 1] $ \i -> do
      rowSum <- reduce 0 [0 .. dimension - 1] $ \acc j -> do
        let indexForPublicKey = (i - j) `mod` dimension
        let pk = publicKey Data.Array.! indexForPublicKey
        let pk' =
              if i < j
                then q - pk
                else pk
        let sig = access2 sigs (t, j)
        return $ acc + (sig * fromIntegral pk')
      let remainder = access2 expectedRemainders (t, i)
      let quotient = access2 expectedQuotients (t, i)

      -- assert the relation between rowSum, remainder and quotient
      assert $ rowSum `eq` (quotient * fromInteger q + remainder)

  forM_ [0 .. dimension - 1] $ \i -> do
    let expected = setupAggSig setup Data.Array.! i
    let actual = foldl (\acc t -> 
                  let remainder = access2 expectedRemainders (t, i)
                  in  acc + remainder) 0 [0 .. numOfSigs - 1] 

    -- assert that the sum of remainders forms a term of aggregate signature
    assert $ actual `eq` fromIntegral expected

checkSize :: (GaloisField n, Integral n) => Param n -> Comp ()
checkSize (Param dimension numOfSigs setup _) = do
  let signatures = setupSignatures setup

  sigBitStrings <- inputs3 numOfSigs dimension 14
  forM_ [0 .. numOfSigs - 1] $ \i -> do
    let signature = signatures !! i
    forM_ [0 .. dimension - 1] $ \j -> do
      let coeff = signature Data.Array.! j

      -- within the range of [0, 16384)
      let value = foldl (\acc k ->
                            let bit = access3 sigBitStrings (i, j, k)
                                bitValue = fromIntegral (2 ^ k :: Integer)
                                prod = fromBool bit * bitValue
                            in  (acc + prod))  0 [0 .. 13]
      assert (fromIntegral coeff `eq` value)

      let bit13 = access3 sigBitStrings (i, j, 13)
      let bit12 = access3 sigBitStrings (i, j, 12)
      let bit11to0 = foldl (\acc k ->
                              let bit = access3 sigBitStrings (i, j, k)
                              in  acc + fromBool bit) 0 [0 .. 11]

      let smallerThan12289 = fromBool bit13 * fromBool bit12 * bit11to0
      assert (smallerThan12289 `eq` 0)

checkLength :: (Integral n, GaloisField n) => Param n -> Comp ()
checkLength (Param dimension numOfSigs _ _) = do
  sigs <- inputs2 numOfSigs dimension :: Comp (Arr (Arr Number))

  -- expecting square of signatures as input
  sigSquares <- inputs2 numOfSigs dimension :: Comp (Arr (Arr Number))
  -- for each signature
  forM_ [0 .. numOfSigs - 1] $ \t -> do
    -- for each term of signature
    forM_ [0 .. dimension - 1] $ \i -> do
      let sig = access2 sigs (t, i)
      let square = access2 sigSquares (t, i)
      assert (square `eq` (sig * sig))

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
    assert $ actualLength `eq` (quotient * fromInteger q + remainder)

aggregateSignature :: (Integral n, GaloisField n) => Param n -> Comp ()
aggregateSignature param = do
  let settings = paramSettings param
  -- check aggregate signature
  void $ case enableAggChecking settings of
    False -> return ()
    True -> checkAgg param

  -- check signature size
  void $ case enableSizeChecking settings of
    False -> return ()
    True -> checkSize param

  -- check squares & length of signatures
  case enableLengthChecking settings of
    False -> return ()
    True -> checkLength param
