module Keelung.Compiler.Compile.UInt.CLMul (compileCLMulU) where

import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import Keelung.Compiler.Compile.Boolean qualified as Boolean
import Keelung.Compiler.Compile.Monad
import Keelung.Data.Reference
import Keelung.Data.U qualified as U
import Keelung.Syntax (Width)

--------------------------------------------------------------------------------

-- Model of carry-less multiplication: see https://en.wikipedia.org/wiki/Carry-less_product

compileCLMulU :: (GaloisField n, Integral n) => Int -> RefU -> Either RefU Integer -> Either RefU Integer -> M n ()
compileCLMulU width out (Right a) (Right b) = do
  let val = U.uValue (U.clMul (U.new width a) (U.new width b))
  writeValU out val
compileCLMulU width out (Right a) (Left b) = do
  temp <- freshRefU width
  writeValU temp a
  compileCLMul width out temp b
compileCLMulU width out (Left a) (Right b) = do
  temp <- freshRefU width
  writeValU temp b
  compileCLMul width out a temp
compileCLMulU width out (Left a) (Left b) = compileCLMul width out a b

compileCLMul :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
compileCLMul width out x y = forM_ [0 .. width - 1] $ \i -> do
  -- pairs of bits to be conjuncted
  let pairs = [(RefUBit width x j, RefUBit width y (i - j)) | j <- [0 .. i]]
  -- conjunct the pairs
  conjunctedPairs <- sequence [Boolean.andBs [Left a, Left b] | (a, b) <- pairs]
  -- xor the conjuncted pairs
  result <- Boolean.xorBs conjunctedPairs
  case result of
    Left var -> writeEqB (RefUBit width out i) var
    Right val -> writeValB (RefUBit width out i) val