module Keelung.Compiler.Compile.UInt
  ( compile,
    wireU,
    assertLTE,
    assertLT,
    assertGTE,
    assertGT,
    assertDivModU,
    assertCLDivModU,
  )
where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Either qualified as Either
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Keelung.Compiler.Compile.Boolean qualified as Boolean
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Compile.UInt.AESMul
import Keelung.Compiler.Compile.UInt.Addition
import Keelung.Compiler.Compile.UInt.Bitwise qualified as Bitwise
import Keelung.Compiler.Compile.UInt.CLMul
import Keelung.Compiler.Compile.UInt.Comparison
import Keelung.Compiler.Compile.UInt.Logical
import Keelung.Compiler.Compile.UInt.Multiplication
import Keelung.Compiler.ConstraintModule qualified as CM
import Keelung.Compiler.Options
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.LC qualified as LC
import Keelung.Data.Reference
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Keelung.Syntax (HasWidth (widthOf))

--------------------------------------------------------------------------------

compile :: (GaloisField n, Integral n) => RefU -> ExprU n -> M n ()
compile out expr = case expr of
  ValU val -> writeRefUVal out val
  VarU width var -> writeRefUEq out (RefUX width var)
  VarUO width var -> writeRefUEq out (RefUO width var)
  VarUI width var -> writeRefUEq out (RefUI width var)
  VarUP width var -> writeRefUEq out (RefUP width var)
  AddU w xs -> do
    mixed <- mapM wireUWithSign (toList xs)
    let (vars, constants) = Either.partitionEithers mixed
    compileAdd w out vars (sum constants)
  MulU w x y -> do
    x' <- wireU x
    y' <- wireU y
    compileMulU w out x' y'
  AESMulU x y -> do
    x' <- wireU x
    y' <- wireU y
    compileAESMulU out x' y'
  CLMulU w x y -> do
    x' <- wireU x
    y' <- wireU y
    compileCLMulU w out x' y'
  CLModU w x y -> do
    x' <- wireU x
    y' <- wireU y
    compileCLMulU w out x' y'
  MMIU w a p -> do
    -- See: https://github.com/btq-ag/keelung-compiler/issues/14
    a' <- wireU a
    compileModInv w out a' p
  AndU w xs -> do
    forM_ [0 .. w - 1] $ \i -> do
      result <- compileExprB (AndB (fmap (`BitU` i) xs))
      case result of
        Left var -> writeRefBEq (RefUBit out i) var
        Right val -> writeRefBVal (RefUBit out i) val
  OrU w xs -> do
    forM_ [0 .. w - 1] $ \i -> do
      result <- compileExprB (OrB (fmap (`BitU` i) xs))
      case result of
        Left var -> writeRefBEq (RefUBit out i) var
        Right val -> writeRefBVal (RefUBit out i) val
  XorU w xs -> do
    xs' <- mapM wireU xs
    compileXorUs w out (toList xs')
  NotU w x -> do
    forM_ [0 .. w - 1] $ \i -> do
      result <- compileExprB (NotB (BitU x i))
      case result of
        Left var -> writeRefBEq (RefUBit out i) var
        Right val -> writeRefBVal (RefUBit out i) val
  IfU w p x y -> do
    p' <- compileExprB p
    x' <- wireU x
    y' <- wireU y
    result <- compileIfU w p' x' y'
    case result of
      Left var -> writeRefUEq out var
      Right val -> writeRefUVal out val
  RoLU w n x -> do
    x' <- wireU x
    Bitwise.compileRotateL w out n x'
  ShLU w n x -> do
    x' <- wireU x
    Bitwise.compileShiftL w out n x'
  SetU w x j b -> do
    x' <- wireU x
    b' <- compileExprB b
    Bitwise.compileSetBit w out j x' b'
  BtoU w x -> do
    x' <- compileExprB x
    Bitwise.compileBtoU w out x'

--------------------------------------------------------------------------------

-- | Compile a UInt expression to either a RefU or a constant
wireU :: (GaloisField n, Integral n) => ExprU n -> M n (Either RefU U)
wireU (ValU val) = return (Right val)
wireU (VarU w ref) = return (Left (RefUX w ref))
wireU (VarUO w ref) = return (Left (RefUO w ref))
wireU (VarUI w ref) = return (Left (RefUI w ref))
wireU (VarUP w ref) = return (Left (RefUP w ref))
wireU expr = do
  out <- freshRefU (widthOf expr)
  compile out expr
  return (Left out)

wireUWithSign :: (GaloisField n, Integral n) => (ExprU n, Bool) -> M n (Either (RefU, Bool) U)
wireUWithSign (ValU val, True) = return (Right val)
wireUWithSign (ValU val, False) = return (Right (-val))
wireUWithSign (others, sign) = do
  result <- wireU others
  case result of
    Left var -> return (Left (var, sign))
    Right val -> return (Right (if sign then val else -val))

--------------------------------------------------------------------------------

-- | Allocate a new RefU with double the width of the given RefU or U
_allocDoubleWidth :: (GaloisField n, Integral n) => Either RefU U -> M n (Either RefU U)
_allocDoubleWidth (Left ref) = do
  let width = widthOf ref
  ref' <- freshRefU (width * 2)
  writeSliceVal (Slice.Slice ref' width (width * 2)) 0 -- upper half
  writeSliceEq (Slice.Slice ref' 0 width) (Slice.fromRefU ref) -- lower half
  return (Left ref')
_allocDoubleWidth (Right val) = return $ Right (U.mapWidth (* 2) val)

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

  -- double the widths of these variables
  dividendRef' <- _allocDoubleWidth dividendRef
  divisorRef' <- _allocDoubleWidth divisorRef
  quotientRef' <- _allocDoubleWidth quotientRef
  remainderRef' <- _allocDoubleWidth remainderRef

  productDQ <- freshRefU (width * 2)
  compileMulU (width * 2) productDQ divisorRef' quotientRef'
  compileSub (width * 2) productDQ dividendRef' remainderRef'

  -- 0 ≤ remainder < divisor
  case (remainderRef', divisorRef') of
    (Left xVar, Left yVar) -> do
      result <- Boolean.computeLTUVarVar xVar yVar
      case result of
        Left var -> writeRefBVal var True
        Right True -> return ()
        Right val -> throwError $ Error.ConflictingValuesB True val
    (Left xVar, Right yVal) -> do
      assertLT (width * 2) (Left xVar) (toInteger yVal)
    (Right xVal, Left yVar) -> do
      assertGT (width * 2) (Left yVar) (toInteger xVal)
    (Right xVal, Right yVal) -> do
      assertLT (width * 2) (Right xVal) (toInteger yVal)
  -- 0 < divisor
  assertGT width divisorRef 0
  -- add hint for DivMod
  addDivModHint dividendRef' divisorRef' quotientRef' remainderRef'

-- -- | Assert that a UInt is less than some constant
-- assertLT :: (GaloisField n, Integral n) => Width -> Either RefU U -> Integer -> M n ()
-- assertLT width a c = do
--   -- check if the bound is within the range of the UInt
--   when (c < 1) $
--     throwError $
--       Error.AssertLTBoundTooSmallError c
--   when (c >= 2 ^ width) $
--     throwError $
--       Error.AssertLTBoundTooLargeError c width
--   -- otherwise, assert that a <= c - 1
--   assertLTE width a (c - 1)

-- | Division with remainder on UInts
-- assertDivModUCC :: (GaloisField n, Integral n) => Width -> U -> U -> Either RefU U -> Either RefU U -> M n ()
-- assertDivModUCC width dividend divisor quotient remainder = do
--   -- 0 < divisor
--   when (divisor == 0) $
--     throwError $
--       Error.AssertComparisonError (toInteger dividend) GT 0

--   --    dividend = divisor * quotient + remainder
--   --  =>
--   --    divisor * quotient = dividend - remainder
--   productDQ <- freshRefU width
--   compileMulU width productDQ (Right divisor) quotient
--   compileSub width productDQ (Right dividend) remainder
--   -- 0 ≤ remainder < divisor
--   assertLT width remainder (toInteger divisor)
--   -- add hint for DivMod
--   addDivModHint (Right dividend) (Right divisor) quotient remainder

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
  compileCLMulU width productDQ divisorRef quotientRef
  compileXorUs width productDQ [dividendRef, remainderRef]

  -- 0 ≤ remainder < divisor
  compileAssertion $ ExprB (LTU remainder divisor)
  -- 0 < divisor
  assertGT width divisorRef 0
  -- add hint for CLDivMod
  addCLDivModHint dividendRef divisorRef quotientRef remainderRef

-- | Assert that a UInt is less than some constant
assertLT :: (GaloisField n, Integral n) => Width -> Either RefU U -> Integer -> M n ()
assertLT width a c = do
  -- check if the bound is within the range of the UInt
  when (c < 1) $
    throwError $
      Error.AssertLTBoundTooSmallError c
  when (c >= 2 ^ width) $
    throwError $
      Error.AssertLTBoundTooLargeError c width
  -- otherwise, assert that a <= c - 1
  assertLTE width a (c - 1)

-- | Assert that a UInt is greater than some constant
assertGT :: (GaloisField n, Integral n) => Width -> Either RefU U -> Integer -> M n ()
assertGT width a c = do
  -- check if the bound is within the range of the UInt
  when (c < 0) $
    throwError $
      Error.AssertGTBoundTooSmallError c
  when (c >= 2 ^ width - 1) $
    throwError $
      Error.AssertGTBoundTooLargeError c width
  -- otherwise, assert that a >= c + 1
  assertGTE width a (c + 1)

-- | Conditional
--  out = p * x + (1 - p) * y
--      =>
--  out = p * x + y - p * y
--      =>
--  (out - y) = p * (x - y)
compileIfU :: (GaloisField n, Integral n) => Width -> Either RefB Bool -> Either RefU U -> Either RefU U -> M n (Either RefU U)
compileIfU _ (Right True) x _ = return x
compileIfU _ (Right False) _ y = return y
compileIfU width (Left p) x y = do
  if x == y
    then return x
    else do
      out <- freshRefU width
      fieldType <- gets (optFieldInfo . CM.cmOptions)
      -- (x - y) * p - out + y = 0
      let outLCs = LC.fromRefU fieldType (Left out)
      let xyLCs =
            zip
              (LC.fromRefU fieldType x)
              (LC.fromRefU fieldType y)
      zipWithM_
        ( \outLC (xLC, yLC) -> do
            case (xLC, yLC) of
              (LC.Constant xVal, LC.Constant yVal) -> do
                -- if both branches are constants, we can express it as addative constraints
                -- (x - y) * p - out + y = 0
                writeAddWithLC $ (xVal - yVal) LC.@ B p <> LC.neg outLC <> yLC
              _ ->
                -- (out - y) = p * (x - y)
                writeMulWithLC (1 LC.@ B p) (xLC <> LC.neg yLC) (outLC <> LC.neg yLC)
        )
        outLCs
        xyLCs
      -- let xLimbs = Limb.refUToLimbs fieldWidth (RefUVal width x)

      -- let bits = [(B (RefUBit out i), -(2 ^ i)) | i <- [0 .. width - 1]]
      -- -- (x - y) * p - out + y = 0
      -- writeAdd (fromInteger y) $ (B p, fromInteger (x - y)) : bits
      return $ Left out

--------------------------------------------------------------------------------

-- | Modular multiplicative inverse.
--  Let a⁻¹ = a `modInv` p:
--  The following constraints should be generated:
--    * a * a⁻¹ = np + 1
--    * n ≤ p
-- See: https://github.com/btq-ag/keelung-compiler/issues/14
compileModInv :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU U -> U -> M n ()
compileModInv width out a p = do
  -- prod = a * out
  prod <- freshRefU width
  compileMulU width prod a (Left out)
  -- prod = np + 1
  n <- freshRefU width
  np <- freshRefU width
  compileMulU width np (Left n) (Right p)
  compileAdd width prod [(np, True)] 1
  -- n ≤ p
  assertLTE width (Left n) (toInteger p)
  addModInvHint a (Left out) (Left n) p