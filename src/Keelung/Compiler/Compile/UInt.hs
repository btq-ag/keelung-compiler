module Keelung.Compiler.Compile.UInt
  ( compile,
    wireU,
    assertLTE,
    assertLT,
    assertGTE,
    assertGT,
    DivMod.assert,
    DivMod.assertCL,
  )
where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Either qualified as Either
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Compile.UInt.AESMul
import Keelung.Compiler.Compile.UInt.Addition
import Keelung.Compiler.Compile.UInt.Bitwise qualified as Bitwise
import Keelung.Compiler.Compile.UInt.CLMul
import Keelung.Compiler.Compile.UInt.Comparison
import Keelung.Compiler.Compile.UInt.DivMod qualified as DivMod
import Keelung.Compiler.Compile.UInt.Logical
import Keelung.Compiler.Compile.UInt.Mul qualified as Mul
import Keelung.Compiler.ConstraintModule qualified as CM
import Keelung.Compiler.Options
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.LC (neg, (@))
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
    compileAdd w out vars (U.slice (0, w)  (sum constants) )
  MulU _ x y -> do
    x' <- wireU x
    y' <- wireU y
    Mul.compile out x' y'
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
  DivModU w x y -> do 
    dividend <- wireU x
    divisor <- wireU y
    quotient <- freshRefU w
    remainder <- freshRefU w
    DivMod.assert w dividend divisor (Left quotient) (Left remainder)
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
  SliceU _ x i j -> do
    result <- wireU x
    case result of
      Left var -> writeSliceEq (Slice.fromRefU out) (Slice.Slice var i j)
      Right val -> writeSliceVal (Slice.fromRefU out) (toInteger (U.slice (i, j) val))
  JoinU _ x y -> do
    let widthX = widthOf x
    let widthY = widthOf y
    resultX <- wireU x
    case resultX of
      Left var -> writeSliceEq (Slice.Slice out 0 widthX) (Slice.fromRefU var)
      Right val -> writeSliceVal (Slice.Slice out 0 widthX) (toInteger val)
    resultY <- wireU y
    case resultY of
      Left var -> writeSliceEq (Slice.Slice out widthX (widthX + widthY)) (Slice.fromRefU var)
      Right val -> writeSliceVal (Slice.Slice out widthX (widthX + widthY)) (toInteger val)

--------------------------------------------------------------------------------

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
                writeAddWithLC $ (xVal - yVal) @ B p <> neg outLC <> yLC
              _ ->
                -- (out - y) = p * (x - y)
                writeMulWithLC (1 @ B p) (xLC <> neg yLC) (outLC <> neg yLC)
        )
        outLCs
        xyLCs
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
  Mul.compile prod a (Left out)
  -- prod = np + 1
  n <- freshRefU width
  np <- freshRefU width
  Mul.compile np (Left n) (Right p)
  compileAdd width prod [(np, True)] 1
  -- n ≤ p
  assertLTE width (Left n) (toInteger p)
  addModInvHint a (Left out) (Left n) p