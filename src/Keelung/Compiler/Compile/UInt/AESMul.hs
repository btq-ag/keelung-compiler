module Keelung.Compiler.Compile.UInt.AESMul (compileAESMulU) where

import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import Keelung.Compiler.Compile.Boolean qualified as Boolean
import Keelung.Compiler.Compile.Monad
import Keelung.Data.Reference
import Keelung.Data.U qualified as U
import Keelung.Syntax (Width)

--------------------------------------------------------------------------------

-- | GF(256) multiplication for AES
--   See https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf for more
compileAESMulU :: (GaloisField n, Integral n) => Int -> RefU -> Either RefU Integer -> Either RefU Integer -> M n ()
compileAESMulU width out (Right a) (Right b) = do
  let val = U.uValue (U.aesMul (U.new width a) (U.new width b))
  writeRefUVal out val
compileAESMulU width out (Right a) (Left b) = compileAESMulCV width out a b
compileAESMulU width out (Left a) (Right b) = compileAESMulCV width out b a
compileAESMulU width out (Left a) (Left b) = compileCLMul width out a b

compileAESMulCV :: (GaloisField n, Integral n) => Width -> RefU -> Integer -> RefU -> M n ()
compileAESMulCV _ out 0 _ = writeRefUVal out 0
compileAESMulCV _ out 1 x = writeRefUEq out x
-- compileAESMulCV width out 2 x = do
--   let shiftedLimb = Limb.new x

--   error "writeRefUEq out x"
compileAESMulCV _ _ _ _ = error "writeRefUEq out x"

-- compileAESMulCV width out constant x = forM_ [0 .. width - 1] $ \i -> do
--   -- pairs of bits to be conjuncted
--   let pairs = [(RefUBit width x j, RefUBit width y (i - j)) | j <- [0 .. i]]
--   -- conjunct the pairs
--   conjunctedPairs <- sequence [Boolean.andBs [Left a, Left b] | (a, b) <- pairs]
--   -- xor the conjuncted pairs
--   result <- Boolean.xorBs conjunctedPairs
--   case result of
--     Left var -> writeRefBEq (RefUBit width out i) var
--     Right val -> writeRefBVal (RefUBit width out i) val

compileCLMul :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
compileCLMul width out x y = forM_ [0 .. width - 1] $ \i -> do
  -- pairs of bits to be conjuncted
  let pairs = [(RefUBit width x j, RefUBit width y (i - j)) | j <- [0 .. i]]
  -- conjunct the pairs
  conjunctedPairs <- sequence [Boolean.andBs [Left a, Left b] | (a, b) <- pairs]
  -- xor the conjuncted pairs
  result <- Boolean.xorBs conjunctedPairs
  case result of
    Left var -> writeRefBEq (RefUBit width out i) var
    Right val -> writeRefBVal (RefUBit width out i) val