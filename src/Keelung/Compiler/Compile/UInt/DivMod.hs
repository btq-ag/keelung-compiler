module Keelung.Compiler.Compile.UInt.DivMod (assert, assertCL) where

import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import Keelung.Compiler.Compile.Boolean qualified as Boolean
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Compile.UInt.Addition
import Keelung.Compiler.Compile.UInt.CLMul qualified as CLMul
import Keelung.Compiler.Compile.UInt.Comparison qualified as Comparison
import Keelung.Compiler.Compile.UInt.Logical qualified as Logical
import Keelung.Compiler.Compile.UInt.Mul qualified as Mul
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.Reference (RefU)
import Keelung.Data.U (U)

--------------------------------------------------------------------------------

-- | Division with remainder on UInts
--    1. dividend = divisor * quotient + remainder
--    2. 0 ≤ remainder < divisor
--    3. 0 < divisor
assert :: (GaloisField n, Integral n) => Width -> Either RefU U -> Either RefU U -> Either RefU U -> Either RefU U -> M n ()
assert width dividend divisor quotient remainder = do
  --    dividend = divisor * quotient + remainder
  --  =>
  --    divisor * quotient = dividend - remainder
  productDQ <- freshRefU (width * 2)
  Mul.compile productDQ divisor quotient
  compileSub (width * 2) productDQ dividend remainder

  -- 0 ≤ remainder < divisor
  case (remainder, divisor) of
    (Left xVar, Left yVar) -> do
      result <- Boolean.computeLTUVarVar xVar yVar
      case result of
        Left var -> writeRefBVal var True
        Right True -> return ()
        Right val -> throwError $ Error.ConflictingValuesB True val
    (Left xVar, Right yVal) -> do
      Comparison.assertLT width (Left xVar) (toInteger yVal)
    (Right xVal, Left yVar) -> do
      Comparison.assertGT width (Left yVar) (toInteger xVal)
    (Right xVal, Right yVal) -> do
      Comparison.assertLT width (Right xVal) (toInteger yVal)
  -- 0 < divisor
  Comparison.assertGT width divisor 0
  -- add hint for DivMod
  addDivModHint dividend divisor quotient remainder

-- | Carry-less division with remainder on UInts
--    1. dividend = divisor .*. quotient .^. remainder
--    2. 0 ≤ remainder < divisor
--    3. 0 < divisor
assertCL :: (GaloisField n, Integral n) => Width -> Either RefU U -> Either RefU U -> Either RefU U -> Either RefU U -> M n ()
assertCL width dividend divisor quotient remainder = do
  --    dividend = divisor .*. quotient .^. remainder
  --  =>
  --    dividend .^. remainder = divisor .*. quotient
  productDQ <- freshRefU width
  CLMul.compileCLMulU width productDQ divisor quotient
  Logical.compileXorUs width productDQ [dividend, remainder]

  -- 0 ≤ remainder < divisor
  case (remainder, divisor) of
    (Left xVar, Left yVar) -> do
      result <- Boolean.computeLTUVarVar xVar yVar
      case result of
        Left var -> writeRefBVal var True
        Right True -> return ()
        Right val -> throwError $ Error.ConflictingValuesB True val
    (Left xVar, Right yVal) -> do
      Comparison.assertLT width (Left xVar) (toInteger yVal)
    (Right xVal, Left yVar) -> do
      Comparison.assertGT width (Left yVar) (toInteger xVal)
    (Right xVal, Right yVal) -> do
      Comparison.assertLT width (Right xVal) (toInteger yVal)
  -- 0 < divisor
  Comparison.assertGT width divisor 0
  -- add hint for CLDivMod
  addCLDivModHint dividend divisor quotient remainder
