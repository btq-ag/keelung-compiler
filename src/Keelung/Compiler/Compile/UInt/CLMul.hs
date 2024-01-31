module Keelung.Compiler.Compile.UInt.CLMul (compileCLMulU) where

import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import Keelung.Compiler.Compile.Boolean qualified as Boolean
import Keelung.Compiler.Compile.Monad
import Keelung.Data.Reference
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Keelung.Syntax (Width)

--------------------------------------------------------------------------------

-- Model of carry-less multiplication: see https://en.wikipedia.org/wiki/Carry-less_product

compileCLMulU :: (GaloisField n, Integral n) => Int -> RefU -> Either RefU U -> Either RefU U -> M n ()
compileCLMulU _ out (Right a) (Right b) = do
  writeRefUVal out (U.clMul a b)
compileCLMulU width out (Right a) (Left b) = do
  temp <- freshRefU width
  writeRefUVal temp a
  compileCLMul width out temp b
compileCLMulU width out (Left a) (Right b) = do
  temp <- freshRefU width
  writeRefUVal temp b
  compileCLMul width out a temp
compileCLMulU width out (Left a) (Left b) = compileCLMul width out a b

--  Elementary school multiplication:
--
--                      x₃    x₂    x₁    x₀
--             ×)       y₃    y₂    y₁    y₀
-- -------------------------------------------
--                      x₃y₀  x₂y₀  x₁y₀  x₀y₀
--                      x₂y₁  x₁y₁  x₀y₁
--                      x₁y₂  x₀y₂
--                      x₀y₃
--
--  1. get pairs of bits to be conjuncted
--  2. conjunct the pairs
--  3. xor the conjuncted pairs
--  4. write the result
compileCLMul :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
compileCLMul width out x y = forM_ [0 .. width - 1] $ \i -> do
  -- pairs of bits to be conjuncted
  let pairs = [(RefUBit x j, RefUBit y (i - j)) | j <- [0 .. i]]
  -- conjunct the pairs
  conjunctedPairs <- sequence [Boolean.andBs [Left a, Left b] | (a, b) <- pairs]
  -- xor the conjuncted pairs
  result <- Boolean.xorBs conjunctedPairs
  case result of
    Left var -> writeRefBEq (RefUBit out i) var
    Right val -> writeRefBVal (RefUBit out i) val