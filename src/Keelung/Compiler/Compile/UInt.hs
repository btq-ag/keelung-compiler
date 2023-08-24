module Keelung.Compiler.Compile.UInt
  ( compileAddU,
    compileSubU,
    compileMulU,
    compileModInv,
    assertLTE,
    assertGTE,
  )
where

import Data.Field.Galois (GaloisField)
import Keelung.Compiler.Compile.UInt.Addition
import Keelung.Compiler.Compile.UInt.Comparison
import Keelung.Compiler.Compile.UInt.Multiplication
import Keelung.Compiler.Compile.Util
import Keelung.Data.Reference
import Keelung.Syntax (Width)

--------------------------------------------------------------------------------

-- | Modular multiplicative inverse.
--  Let a⁻¹ = a `modInv` p:
--  The following constraints should be generated:
--    * a * a⁻¹ = np + 1
--    * n ≤ p
-- See: https://github.com/btq-ag/keelung-compiler/issues/14
compileModInv :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU Integer -> Integer -> M n ()
compileModInv width out a p = do
  -- prod = a * out
  prod <- freshRefU (width * 2)
  compileMulU width prod a (Left out)
  -- prod = np + 1
  n <- freshRefU width
  np <- freshRefU (width * 2)
  compileMulU (width * 2) np (Left n) (Right p)
  compileAddU (width * 2) prod [(np, True)] 1
  -- n ≤ p
  assertLTE width (Left n) p
  addModInvHint (width * 2) a (Left out) (Left n) p