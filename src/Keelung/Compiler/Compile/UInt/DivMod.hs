module Keelung.Compiler.Compile.UInt.DivMod (assertDivModU, assertCLDivModU) where

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

--------------------------------------------------------------------------------

-- | Division with remainder on UInts
--    1. dividend = divisor * quotient + remainder
--    2. 0 ≤ remainder < divisor
--    3. 0 < divisor
assertDivModU :: (GaloisField n, Integral n) => Width -> ExprU n -> ExprU n -> ExprU n -> ExprU n -> M n ()
assertDivModU width dividend divisor quotient remainder = do
  --    dividend = divisor * quotient + remainder
  --  =>
  --    divisor * quotient = dividend - remainder
  dividendRef <- wireU dividend
  divisorRef <- wireU divisor
  quotientRef <- wireU quotient
  remainderRef <- wireU remainder

  productDQ <- freshRefU (width * 2)
  Mul.compile productDQ divisorRef quotientRef
  compileSub (width * 2) productDQ dividendRef remainderRef

  -- 0 ≤ remainder < divisor
  case (remainderRef, divisorRef) of
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
  Comparison.assertGT width divisorRef 0
  -- add hint for DivMod
  addDivModHint dividendRef divisorRef quotientRef remainderRef

-- | Carry-less division with remainder on UInts
--    1. dividend = divisor .*. quotient .^. remainder
--    2. 0 ≤ remainder < divisor
--    3. 0 < divisor
assertCLDivModU :: (GaloisField n, Integral n) => (Expr n -> M n ()) -> Width -> ExprU n -> ExprU n -> ExprU n -> ExprU n -> M n ()
assertCLDivModU compileAssertion width dividend divisor quotient remainder = do
  --    dividend = divisor .*. quotient .^. remainder
  --  =>
  --    dividend .^. remainder = divisor .*. quotient
  dividendRef <- wireU dividend
  divisorRef <- wireU divisor
  quotientRef <- wireU quotient
  remainderRef <- wireU remainder

  productDQ <- freshRefU width
  CLMul.compileCLMulU width productDQ divisorRef quotientRef
  Logical.compileXorUs width productDQ [dividendRef, remainderRef]

  -- 0 ≤ remainder < divisor
  compileAssertion $ ExprB (LTU remainder divisor)
  -- 0 < divisor
  Comparison.assertGT width divisorRef 0
  -- add hint for CLDivMod
  addCLDivModHint dividendRef divisorRef quotientRef remainderRef
