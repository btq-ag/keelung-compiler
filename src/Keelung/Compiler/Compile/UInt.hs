module Keelung.Compiler.Compile.UInt
  ( compile,
    wireU,
    assertLTE,
    assertLT,
    assertGTE,
    assertGT,
    assertDivModU,
  )
where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Bits qualified
import Data.Either qualified as Either
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.UInt.Addition
import Keelung.Compiler.Compile.UInt.Comparison
import Keelung.Compiler.Compile.UInt.Multiplication
import Keelung.Compiler.Compile.Util
import Keelung.Compiler.ConstraintModule (ConstraintModule (cmField))
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.FieldInfo qualified as FieldInfo
import Keelung.Data.Reference
import Keelung.Syntax (HasWidth (widthOf))

--------------------------------------------------------------------------------

compile :: (GaloisField n, Integral n) => RefU -> ExprU n -> M n ()
compile out expr = case expr of
  ValU width val -> writeValU width out val
  VarU width var -> do
    -- fieldWidth <- gets (FieldInfo.fieldWidth . cmField)
    -- zipWithM_ writeEqL (refUToLimbs fieldWidth (RefUX width var)) (refUToLimbs fieldWidth out)
    -- writeEqU width out (RefUX width var)
    writeEqU2 out (RefUX width var)
  VarUO width var -> do
    fieldWidth <- gets (FieldInfo.fieldWidth . cmField)
    zipWithM_ writeEqL (refUToLimbs fieldWidth (RefUO width var)) (refUToLimbs fieldWidth out)
  -- writeEqU2 out (RefUO width var)
  VarUI width var -> do
    fieldWidth <- gets (FieldInfo.fieldWidth . cmField)
    zipWithM_ writeEqL (refUToLimbs fieldWidth (RefUI width var)) (refUToLimbs fieldWidth out)
  VarUP width var -> do
    fieldWidth <- gets (FieldInfo.fieldWidth . cmField)
    zipWithM_ writeEqL (refUToLimbs fieldWidth (RefUP width var)) (refUToLimbs fieldWidth out)
  AddU w xs -> do
    mixed <- mapM wireUWithSign (toList xs)
    let (vars, constants) = Either.partitionEithers mixed
    compileAddU w out vars (sum constants)
  MulU w x y -> do
    x' <- wireU x
    y' <- wireU y
    compileMulU w out x' y'
  MMIU w a p -> do
    -- See: https://github.com/btq-ag/keelung-compiler/issues/14
    a' <- wireU a
    compileModInv w out a' p
  AndU w xs -> do
    forM_ [0 .. w - 1] $ \i -> do
      result <- compileExprB (AndB (fmap (`BitU` i) xs))
      case result of
        Left var -> writeEqB (RefUBit w out i) var
        Right val -> writeValB (RefUBit w out i) val
  OrU w xs -> do
    forM_ [0 .. w - 1] $ \i -> do
      result <- compileExprB (OrB (fmap (`BitU` i) xs))
      case result of
        Left var -> writeEqB (RefUBit w out i) var
        Right val -> writeValB (RefUBit w out i) val
  XorU w x y -> do
    forM_ [0 .. w - 1] $ \i -> do
      result <- compileExprB (XorB (BitU x i) (BitU y i))
      case result of
        Left var -> writeEqB (RefUBit w out i) var
        Right val -> writeValB (RefUBit w out i) val
  NotU w x -> do
    forM_ [0 .. w - 1] $ \i -> do
      result <- compileExprB (NotB (BitU x i))
      case result of
        Left var -> writeEqB (RefUBit w out i) var
        Right val -> writeValB (RefUBit w out i) val
  IfU w p x y -> do
    p' <- compileExprB p
    x' <- wireU x
    y' <- wireU y
    result <- compileIfU w p' x' y'
    case result of
      Left var -> writeEqU w out var
      Right val -> writeValU w out val
  RoLU w n x -> do
    result <- wireU x
    case result of
      Left var -> do
        forM_ [0 .. w - 1] $ \i -> do
          let i' = (i - n) `mod` w
          writeEqB (RefUBit w out i) (RefUBit w var i') -- out[i] = x[i']
      Right val -> do
        forM_ [0 .. w - 1] $ \i -> do
          let i' = (i - n) `mod` w
          writeValB (RefUBit w out i) (Data.Bits.testBit val i') -- out[i] = val[i']
  ShLU w n x -> do
    x' <- wireU x
    case compare n 0 of
      EQ -> case x' of
        Left var -> writeEqU w out var
        Right val -> writeValU w out val
      GT -> do
        -- fill lower bits with 0s
        forM_ [0 .. n - 1] $ \i -> do
          writeValB (RefUBit w out i) False -- out[i] = 0
          -- shift upper bits
        forM_ [n .. w - 1] $ \i -> do
          let i' = i - n
          case x' of
            Left var -> writeEqB (RefUBit w out i) (RefUBit w var i') -- out[i] = x'[i']
            Right val -> writeValB (RefUBit w out i) (Data.Bits.testBit val i') -- out[i] = x'[i']
      LT -> do
        -- shift lower bits
        forM_ [0 .. w + n - 1] $ \i -> do
          let i' = i - n
          case x' of
            Left var -> writeEqB (RefUBit w out i) (RefUBit w var i') -- out[i] = x'[i']
            Right val -> writeValB (RefUBit w out i) (Data.Bits.testBit val i') -- out[i] = x'[i']
            -- fill upper bits with 0s
        forM_ [w + n .. w - 1] $ \i -> do
          writeValB (RefUBit w out i) False -- out[i] = 0
  SetU w x j b -> do
    x' <- wireU x
    b' <- compileExprB b
    forM_ [0 .. w - 1] $ \i -> do
      if i == j
        then case b' of
          Left var -> writeEqB (RefUBit w out i) var
          Right val -> writeValB (RefUBit w out i) val
        else do
          case x' of
            Left var -> writeEqB (RefUBit w out i) (RefUBit w var i) -- out[i] = x'[i]
            Right val -> writeValB (RefUBit w out i) (Data.Bits.testBit val i) -- out[i] = x'[i]
  BtoU w x -> do
    -- 1. wire 'out[ZERO]' to 'x'
    result <- compileExprB x

    case result of
      Left var -> writeEqB (RefUBit w out 0) var -- out[0] = x
      Right val -> writeValB (RefUBit w out 0) val -- out[0] = x
      -- 2. wire 'out[SUCC _]' to '0' for all other bits
    forM_ [1 .. w - 1] $ \i ->
      writeValB (RefUBit w out i) False -- out[i] = 0

--------------------------------------------------------------------------------

wireU :: (GaloisField n, Integral n) => ExprU n -> M n (Either RefU Integer)
wireU (ValU _ val) = return (Right val)
wireU (VarU w ref) = return (Left (RefUX w ref))
wireU (VarUO w ref) = return (Left (RefUO w ref))
wireU (VarUI w ref) = return (Left (RefUI w ref))
wireU (VarUP w ref) = return (Left (RefUP w ref))
wireU expr = do
  out <- freshRefU (widthOf expr)
  compile out expr
  return (Left out)

wireUWithSign :: (GaloisField n, Integral n) => (ExprU n, Bool) -> M n (Either (RefU, Bool) Integer)
wireUWithSign (ValU _ val, True) = return (Right val)
wireUWithSign (ValU _ val, False) = return (Right (-val))
wireUWithSign (others, sign) = do
  result <- wireU others
  case result of
    Left var -> return (Left (var, sign))
    Right val -> return (Right (if sign then val else -val))

--------------------------------------------------------------------------------

-- | Division with remainder on UInts
--    1. dividend = divisor * quotient + remainder
--    2. 0 ≤ remainder < divisor
--    3. 0 < divisor
assertDivModU :: (GaloisField n, Integral n) => (Expr n -> M n ()) -> Width -> ExprU n -> ExprU n -> ExprU n -> ExprU n -> M n ()
assertDivModU compileAssertion width dividend divisor quotient remainder = do
  --    dividend = divisor * quotient + remainder
  --  =>
  --    divisor * quotient = dividend - remainder
  dividendRef <- wireU dividend
  divisorRef <- wireU divisor
  quotientRef <- wireU quotient
  remainderRef <- wireU remainder

  productDQ <- freshRefU width
  compileMulU width productDQ divisorRef quotientRef
  compileSubU width productDQ dividendRef remainderRef

  -- 0 ≤ remainder < divisor
  compileAssertion $ ExprB (LTU remainder divisor)
  -- 0 < divisor
  assertGT width divisorRef 0
  -- add hint for DivMod
  addDivModHint width dividendRef divisorRef quotientRef remainderRef

-- | Assert that a UInt is less than some constant
assertLT :: (GaloisField n, Integral n) => Width -> Either RefU Integer -> Integer -> M n ()
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
assertGT :: (GaloisField n, Integral n) => Width -> Either RefU Integer -> Integer -> M n ()
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
compileIfU :: (GaloisField n, Integral n) => Width -> Either RefB Bool -> Either RefU Integer -> Either RefU Integer -> M n (Either RefU Integer)
compileIfU _ (Right True) x _ = return x
compileIfU _ (Right False) _ y = return y
compileIfU width (Left p) (Right x) (Right y) = do
  if x == y
    then return $ Right x
    else do
      out <- freshRefU width
      let bits = [(B (RefUBit width out i), -(2 ^ i)) | i <- [0 .. width - 1]]
      -- (x - y) * p - out + y = 0
      writeAdd (fromInteger y) $ (B p, fromInteger (x - y)) : bits
      return $ Left out
compileIfU width (Left p) (Right x) (Left y) = do
  out <- freshRefU width
  let bitsY = [(B (RefUBit width y i), -(2 ^ i)) | i <- [0 .. width - 1]]
  let bitsOut = [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]
  -- (out - y) = p * (x - y)
  writeMul
    (0, [(B p, 1)])
    (fromInteger x, bitsY)
    (0, bitsY <> bitsOut)
  return $ Left out
compileIfU width (Left p) (Left x) (Right y) = do
  out <- freshRefU width
  let bitsX = [(B (RefUBit width x i), 2 ^ i) | i <- [0 .. width - 1]]
  let bitsOut = [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]
  -- (out - y) = p * (x - y)
  writeMul
    (0, [(B p, 1)])
    (fromInteger (-y), bitsX)
    (fromInteger (-y), bitsOut)
  return $ Left out
compileIfU width (Left p) (Left x) (Left y) = do
  out <- freshRefU width
  let bitsOut = [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]
  let bitsX = [(B (RefUBit width x i), 2 ^ i) | i <- [0 .. width - 1]]
  let bitsY = [(B (RefUBit width y i), -(2 ^ i)) | i <- [0 .. width - 1]]
  -- (out - y) = p * (x - y)
  writeMul
    (0, [(B p, 1)])
    (0, bitsX <> bitsY)
    (0, bitsOut <> bitsY)
  return $ Left out

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