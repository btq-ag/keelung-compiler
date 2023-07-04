{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile (run) where

import Control.Arrow (left)
import Control.Monad
import Control.Monad.Except
-- import Keelung.Compiler.Syntax.FieldBits (FieldBits (..))

import Data.Bits qualified
import Data.Either (partitionEithers)
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq (..))
import Keelung.Compiler.Compile.Boolean qualified as Error.Boolean
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.LC
import Keelung.Compiler.Compile.UInt qualified as UInt
import Keelung.Compiler.Compile.Util
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintModule
import Keelung.Compiler.Error
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.FieldInfo (FieldInfo)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Syntax (widthOf)

--------------------------------------------------------------------------------

-- | Compile an untyped expression to a constraint system
run :: (GaloisField n, Integral n) => FieldInfo -> Internal n -> Either (Error n) (ConstraintModule n)
run fieldInfo (Internal untypedExprs _ counters assertions sideEffects) = left CompileError $ runM fieldInfo counters $ do
  forM_ untypedExprs $ \(var, expr) -> do
    case expr of
      ExprB x -> do
        let out = RefBO var
        result <- compileExprB x
        case result of
          Left var' -> writeEqB out var'
          Right val -> writeValB out val
      ExprF x -> do
        let out = RefFO var
        result <- compileExprF x
        handleLC (F out) result
      ExprU x -> do
        let out = RefUO (widthOf x) var
        compileExprU out x

  -- compile assertions to constraints
  mapM_ compileAssertion assertions

  -- compile all side effects
  mapM_ compileSideEffect sideEffects

-- | Compile side effects
compileSideEffect :: (GaloisField n, Integral n) => SideEffect n -> M n ()
compileSideEffect (AssignmentB var val) = do
  result <- compileExprB val
  case result of
    Left var' -> writeEqB (RefBX var) var'
    Right val' -> writeValB (RefBX var) val'
compileSideEffect (AssignmentF var val) = do
  result <- compileExprF val
  handleLC (F (RefFX var)) result
compileSideEffect (AssignmentU width var val) = compileExprU (RefUX width var) val
compileSideEffect (DivMod width dividend divisor quotient remainder) = assertDivModU width dividend divisor quotient remainder
compileSideEffect (AssertLTE width value bound) = do
  x <- wireU value
  UInt.assertLTE width x bound
compileSideEffect (AssertLT width value bound) = do
  x <- wireU value
  assertLT width x bound
compileSideEffect (AssertGTE width value bound) = do
  x <- wireU value
  UInt.assertGTE width x bound
compileSideEffect (AssertGT width value bound) = do
  x <- wireU value
  assertGT width x bound

-- | Compile the constraint 'out = x'.
compileAssertion :: (GaloisField n, Integral n) => Expr n -> M n ()
compileAssertion expr = case expr of
  ExprB (EqB x y) -> assertEqB x y
  ExprB (EqF x y) -> assertEqF x y
  ExprB (EqU x y) -> assertEqU x y
  -- rewriting `assert (x <= y)` width `UInt.assertLTE x y`
  ExprB (LTEU x (ValU width bound)) -> do
    x' <- wireU x
    UInt.assertLTE width x' (toInteger bound)
  ExprB (LTEU (ValU width bound) x) -> do
    x' <- wireU x
    UInt.assertGTE width x' (toInteger bound)
  ExprB (LTU x (ValU width bound)) -> do
    x' <- wireU x
    assertLT width x' (toInteger bound)
  ExprB (LTU (ValU width bound) x) -> do
    x' <- wireU x
    assertGT width x' (toInteger bound)
  ExprB (GTEU x (ValU width bound)) -> do
    x' <- wireU x
    UInt.assertGTE width x' (toInteger bound)
  ExprB (GTEU (ValU width bound) x) -> do
    x' <- wireU x
    UInt.assertLTE width x' (toInteger bound)
  ExprB (GTU x (ValU width bound)) -> do
    x' <- wireU x
    assertGT width x' (toInteger bound)
  ExprB (GTU (ValU width bound) x) -> do
    x' <- wireU x
    assertLT width x' (toInteger bound)
  ExprB x -> do
    -- out <- freshRefB
    result <- compileExprB x
    case result of
      Left var -> writeValB var True
      Right True -> return ()
      Right val -> throwError $ Error.ConflictingValuesB True val
  ExprF x -> do
    result <- compileExprF x
    assertLC 1 result
  ExprU x -> do
    let width = widthOf x
    out <- freshRefU width
    compileExprU out x
    writeValU width out 1

-- | Assert that two Boolean expressions are equal
assertEqB :: (GaloisField n, Integral n) => ExprB n -> ExprB n -> M n ()
assertEqB (ValB a) (ValB b) = when (a /= b) $ throwError $ Error.ConflictingValuesB a b
assertEqB (ValB a) (VarB b) = writeValB (RefBX b) a
assertEqB (ValB a) (VarBO b) = writeValB (RefBO b) a
assertEqB (ValB a) (VarBI b) = writeValB (RefBI b) a
assertEqB (ValB a) (VarBP b) = writeValB (RefBP b) a
assertEqB (ValB a) b = do
  result <- compileExprB b
  case result of
    Left var -> writeValB var a
    Right val -> when (a /= val) $ throwError $ Error.ConflictingValuesB a val
assertEqB (VarB a) (ValB b) = writeValB (RefBX a) b
assertEqB (VarB a) (VarB b) = writeEqB (RefBX a) (RefBX b)
assertEqB (VarB a) (VarBO b) = writeEqB (RefBX a) (RefBO b)
assertEqB (VarB a) (VarBI b) = writeEqB (RefBX a) (RefBI b)
assertEqB (VarB a) (VarBP b) = writeEqB (RefBX a) (RefBP b)
assertEqB (VarB a) b = do
  result <- compileExprB b
  case result of
    Left var -> writeEqB (RefBX a) var
    Right val -> writeValB (RefBX a) val
assertEqB (VarBO a) (ValB b) = writeValB (RefBO a) b
assertEqB (VarBO a) (VarB b) = writeEqB (RefBO a) (RefBX b)
assertEqB (VarBO a) (VarBO b) = writeEqB (RefBO a) (RefBO b)
assertEqB (VarBO a) (VarBI b) = writeEqB (RefBO a) (RefBI b)
assertEqB (VarBO a) (VarBP b) = writeEqB (RefBO a) (RefBP b)
assertEqB (VarBO a) b = do
  result <- compileExprB b
  case result of
    Left var -> writeEqB (RefBO a) var
    Right val -> writeValB (RefBO a) val
assertEqB (VarBI a) (ValB b) = writeValB (RefBI a) b
assertEqB (VarBI a) (VarB b) = writeEqB (RefBI a) (RefBX b)
assertEqB (VarBI a) (VarBO b) = writeEqB (RefBI a) (RefBO b)
assertEqB (VarBI a) (VarBI b) = writeEqB (RefBI a) (RefBI b)
assertEqB (VarBI a) (VarBP b) = writeEqB (RefBI a) (RefBP b)
assertEqB (VarBI a) b = do
  result <- compileExprB b
  case result of
    Left var -> writeEqB (RefBI a) var
    Right val -> writeValB (RefBI a) val
assertEqB (VarBP a) (ValB b) = writeValB (RefBP a) b
assertEqB (VarBP a) (VarB b) = writeEqB (RefBP a) (RefBX b)
assertEqB (VarBP a) (VarBO b) = writeEqB (RefBP a) (RefBO b)
assertEqB (VarBP a) (VarBI b) = writeEqB (RefBP a) (RefBI b)
assertEqB (VarBP a) (VarBP b) = writeEqB (RefBP a) (RefBP b)
assertEqB (VarBP a) b = do
  result <- compileExprB b
  case result of
    Left var -> writeEqB (RefBI a) var
    Right val -> writeValB (RefBI a) val
assertEqB a b = do
  a' <- compileExprB a
  b' <- compileExprB b
  case (a', b') of
    (Left varA, Left varB) -> writeEqB varA varB
    (Left varA, Right valB) -> writeValB varA valB
    (Right valA, Left varB) -> writeValB varB valA
    (Right valA, Right valB) -> when (valA /= valB) $ throwError $ Error.ConflictingValuesB valA valB

-- | Assert that two Field expressions are equal
assertEqF :: (GaloisField n, Integral n) => ExprF n -> ExprF n -> M n ()
assertEqF (ValF a) (ValF b) = when (a /= b) $ throwError $ Error.ConflictingValuesF a b
assertEqF (ValF a) (VarF b) = writeValF (RefFX b) a
assertEqF (ValF a) (VarFO b) = writeValF (RefFO b) a
assertEqF (ValF a) (VarFI b) = writeValF (RefFI b) a
assertEqF (ValF a) (VarFP b) = writeValF (RefFP b) a
assertEqF (ValF a) b = do
  result <- compileExprF b
  assertLC a result
assertEqF (VarF a) (ValF b) = writeValF (RefFX a) b
assertEqF (VarF a) (VarF b) = writeEqF (RefFX a) (RefFX b)
assertEqF (VarF a) (VarFO b) = writeEqF (RefFX a) (RefFO b)
assertEqF (VarF a) (VarFI b) = writeEqF (RefFX a) (RefFI b)
assertEqF (VarF a) (VarFP b) = writeEqF (RefFX a) (RefFP b)
assertEqF (VarF a) b = do
  result <- compileExprF b
  handleLC (F (RefFX a)) result
assertEqF (VarFO a) (ValF b) = writeValF (RefFO a) b
assertEqF (VarFO a) (VarF b) = writeEqF (RefFO a) (RefFX b)
assertEqF (VarFO a) (VarFO b) = writeEqF (RefFO a) (RefFO b)
assertEqF (VarFO a) (VarFI b) = writeEqF (RefFO a) (RefFI b)
assertEqF (VarFO a) (VarFP b) = writeEqF (RefFO a) (RefFP b)
assertEqF (VarFO a) b = do
  result <- compileExprF b
  handleLC (F (RefFO a)) result
assertEqF (VarFI a) (ValF b) = writeValF (RefFI a) b
assertEqF (VarFI a) (VarF b) = writeEqF (RefFI a) (RefFX b)
assertEqF (VarFI a) (VarFO b) = writeEqF (RefFI a) (RefFO b)
assertEqF (VarFI a) (VarFI b) = writeEqF (RefFI a) (RefFI b)
assertEqF (VarFI a) (VarFP b) = writeEqF (RefFI a) (RefFP b)
assertEqF (VarFI a) b = do
  result <- compileExprF b
  handleLC (F (RefFI a)) result
assertEqF (VarFP a) (ValF b) = writeValF (RefFP a) b
assertEqF (VarFP a) (VarF b) = writeEqF (RefFP a) (RefFX b)
assertEqF (VarFP a) (VarFO b) = writeEqF (RefFP a) (RefFO b)
assertEqF (VarFP a) (VarFI b) = writeEqF (RefFP a) (RefFI b)
assertEqF (VarFP a) (VarFP b) = writeEqF (RefFP a) (RefFP b)
assertEqF (VarFP a) b = do
  result <- compileExprF b
  handleLC (F (RefFP a)) result
assertEqF a b = do
  resultA <- compileExprF a
  resultB <- compileExprF b

  case (resultA, resultB) of
    (Constant valA, _) -> do
      assertLC valA resultB
    (Polynomial as, Constant valB) -> do
      assertLC valB (Polynomial as)
    (Polynomial as, Polynomial bs) -> do
      writeAddWithPoly $ PolyG.merge as bs

-- | Assert that two UInt expressions are equal
assertEqU :: (GaloisField n, Integral n) => ExprU n -> ExprU n -> M n ()
assertEqU (ValU _ a) (ValU _ b) = when (a /= b) $ throwError $ Error.ConflictingValuesU a b
assertEqU (ValU w a) (VarU _ b) = writeValU w (RefUX w b) a
assertEqU (ValU w a) (VarUO _ b) = writeValU w (RefUO w b) a
assertEqU (ValU w a) (VarUI _ b) = writeValU w (RefUI w b) a
assertEqU (ValU w a) (VarUP _ b) = writeValU w (RefUP w b) a
assertEqU (ValU w a) b = do
  out <- freshRefU w
  compileExprU out b
  writeValU w out a
assertEqU (VarU w a) (ValU _ b) = writeValU w (RefUX w a) b
assertEqU (VarU w a) (VarU _ b) = writeEqU w (RefUX w a) (RefUX w b)
assertEqU (VarU w a) (VarUO _ b) = writeEqU w (RefUX w a) (RefUO w b)
assertEqU (VarU w a) (VarUI _ b) = writeEqU w (RefUX w a) (RefUI w b)
assertEqU (VarU w a) (VarUP _ b) = writeEqU w (RefUX w a) (RefUP w b)
assertEqU (VarU w a) b = do
  out <- freshRefU w
  compileExprU out b
  writeEqU w (RefUX w a) out
assertEqU (VarUO w a) (ValU _ b) = writeValU w (RefUO w a) b
assertEqU (VarUO w a) (VarU _ b) = writeEqU w (RefUO w a) (RefUX w b)
assertEqU (VarUO w a) (VarUO _ b) = writeEqU w (RefUO w a) (RefUO w b)
assertEqU (VarUO w a) (VarUI _ b) = writeEqU w (RefUO w a) (RefUI w b)
assertEqU (VarUO w a) (VarUP _ b) = writeEqU w (RefUO w a) (RefUP w b)
assertEqU (VarUO w a) b = do
  out <- freshRefU w
  compileExprU out b
  writeEqU w (RefUO w a) out
assertEqU (VarUI w a) (ValU _ b) = writeValU w (RefUI w a) b
assertEqU (VarUI w a) (VarU _ b) = writeEqU w (RefUI w a) (RefUX w b)
assertEqU (VarUI w a) (VarUO _ b) = writeEqU w (RefUI w a) (RefUO w b)
assertEqU (VarUI w a) (VarUI _ b) = writeEqU w (RefUI w a) (RefUI w b)
assertEqU (VarUI w a) (VarUP _ b) = writeEqU w (RefUI w a) (RefUP w b)
assertEqU (VarUI w a) b = do
  out <- freshRefU w
  compileExprU out b
  writeEqU w (RefUI w a) out
assertEqU (VarUP w a) (ValU _ b) = writeValU w (RefUP w a) b
assertEqU (VarUP w a) (VarU _ b) = writeEqU w (RefUP w a) (RefUX w b)
assertEqU (VarUP w a) (VarUO _ b) = writeEqU w (RefUP w a) (RefUO w b)
assertEqU (VarUP w a) (VarUI _ b) = writeEqU w (RefUP w a) (RefUI w b)
assertEqU (VarUP w a) (VarUP _ b) = writeEqU w (RefUP w a) (RefUP w b)
assertEqU (VarUP w a) b = do
  out <- freshRefU w
  compileExprU out b
  writeEqU w (RefUP w a) out
assertEqU a b = do
  let width = widthOf a
  a' <- freshRefU width
  b' <- freshRefU width
  compileExprU a' a
  compileExprU b' b
  writeEqU width a' b'

----------------------------------------------------------------

compileExprB :: (GaloisField n, Integral n) => ExprB n -> M n (Either RefB Bool)
compileExprB = Error.Boolean.compileExprB wireU compileExprF

compileExprF :: (GaloisField n, Integral n) => ExprF n -> M n (LC n)
compileExprF expr = case expr of
  ValF val -> return $ Constant val
  VarF var -> return $ 1 @ F (RefFX var)
  VarFO var -> return $ 1 @ F (RefFO var)
  VarFI var -> return $ 1 @ F (RefFI var)
  VarFP var -> return $ 1 @ F (RefFP var)
  SubF x y -> do
    x' <- toLC x
    y' <- toLC y
    return $ x' <> neg y'
  AddF x y rest -> do
    operands <- mapM toLC (toList (x :<| y :<| rest))
    return $ mconcat operands
  MulF x y -> do
    x' <- toLC x
    y' <- toLC y
    out' <- freshRefF
    let result = 1 @ F out'
    writeMulWithLC x' y' result
    return result
  ExpF x n -> do
    base <- toLC x
    fastExp base 1 n
  DivF x y -> do
    x' <- toLC x
    y' <- toLC y
    out' <- freshRefF
    let result = 1 @ F out'
    writeMulWithLC y' result x'
    return result
  IfF p x y -> do
    p' <- compileExprB p
    x' <- toLC x
    y' <- toLC y
    compileIfF p' x' y'
  BtoF x -> do
    result <- compileExprB x
    case result of
      Left var -> return $ 1 @ B var
      Right True -> return $ Constant 1
      Right False -> return $ Constant 0

compileExprU :: (GaloisField n, Integral n) => RefU -> ExprU n -> M n ()
compileExprU out expr = case expr of
  ValU width val -> writeValU width out val
  VarU width var -> writeEqU width out (RefUX width var)
  VarUO width var -> writeEqU width out (RefUX width var)
  VarUI width var -> writeEqU width out (RefUI width var)
  VarUP width var -> writeEqU width out (RefUP width var)
  AddU w xs -> do
    mixed <- mapM wireUWithSign (toList xs)
    let (vars, constants) = partitionEithers mixed
    UInt.compileAddU w out vars (sum constants)
  MulU w x y -> do
    x' <- wireU x
    y' <- wireU y
    UInt.compileMulU w out x' y'
  MMIU w a p -> do
    -- See: https://github.com/btq-ag/keelung-compiler/issues/14
    a' <- wireU a
    nRef <- freshRefU w
    -- 1. a * a⁻¹ = np + 1
    aainv <- freshRefU (w * 2)
    compileMulU2 w aainv a' (Left out) -- a * a⁻¹
    np <- freshRefU (w * 2)
    compileMulU2 w np (Left nRef) (Right (fromInteger p))
    compileAddU2 w aainv (Left np) (Right 1)
    -- 2. n ≤ p
    UInt.assertLTE w (Left nRef) p
    addModInvHint w a' (Left out) (Left nRef) p

  -- writeMul (0, [(U var, 1)]) (0, [(U out, 1)]) (1, [(U nRef, fromInteger p)])
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
  compileExprU out expr
  return (Left out)

wireUWithSign :: (GaloisField n, Integral n) => (ExprU n, Bool) -> M n (Either (RefU, Bool) Integer)
wireUWithSign (ValU _ val, True) = return (Right val)
wireUWithSign (ValU _ val, False) = return (Right (-val))
wireUWithSign (others, sign) = do
  result <- wireU others
  case result of
    Left var -> return (Left (var, sign))
    Right val -> return (Right (if sign then val else -val))

compileAddOrSubU2 :: (GaloisField n, Integral n) => Bool -> Width -> RefU -> Either RefU Integer -> Either RefU Integer -> M n ()
compileAddOrSubU2 isSub width out (Right a) (Right b) = do
  let val = if isSub then a - b else a + b
  writeValU (width * 2) out val
compileAddOrSubU2 isSub width out (Right a) (Left b) = do
  let bs = [(B (RefUBit width b i), if isSub then -(2 ^ i) else 2 ^ i) | i <- [0 .. width - 1]]
  let outputBits = [(B (RefUBit (width * 2) out i), -(2 ^ i)) | i <- [0 .. width * 2 - 1]]
  writeAdd (fromInteger a) $ bs <> outputBits
compileAddOrSubU2 isSub width out (Left a) (Right b) = do
  let as = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
  let outputBits = [(B (RefUBit (width * 2) out i), -(2 ^ i)) | i <- [0 .. width * 2 - 1]]
  writeAdd (fromInteger $ if isSub then -b else b) $ as <> outputBits
compileAddOrSubU2 isSub width out (Left a) (Left b) = do
  -- out + carry = A + B
  let as = [(B (RefUBit width a i), -(2 ^ i)) | i <- [0 .. width - 1]]
  let bs = [(B (RefUBit width b i), if isSub then 2 ^ i else -(2 ^ i)) | i <- [0 .. width - 1]]
  let outputBits = [(B (RefUBit (width * 2) out i), -(2 ^ i)) | i <- [0 .. width * 2 - 1]]

  writeAdd 0 $ as <> bs <> outputBits

compileAddU2 :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU Integer -> Either RefU Integer -> M n ()
compileAddU2 = compileAddOrSubU2 False

compileMulBigCC :: (GaloisField n, Integral n) => Int -> RefU -> Integer -> Integer -> M n ()
compileMulBigCC width out a b = do
  let val = a * b
  writeValU width out val

-- | Encoding addition on UInts with multiple operands: O(2)
--      A       =   2ⁿAₙ₋₁ + ... + 2A₁ + A₀
--      B       =   2ⁿBₙ₋₁ + ... + 2B₁ + B₀
--      C       = 2²ⁿC₂ₙ₋₁ + ... + 2C₁ + C₀
--      Result  =   2ⁿCₙ₋₁ + ... + 2C₁ + C₀
compileMulU :: (GaloisField n, Integral n) => Int -> RefU -> Either RefU Integer -> Either RefU Integer -> M n ()
compileMulU width out (Right a) (Right b) = do
  -- let val = a * b
  -- writeValU width out val
  compileMulBigCC width out a b
compileMulU width out (Right a) (Left b) = do
  carry <- replicateM width (B <$> freshRefB)
  let bs = [(B (RefUBit width b i), 2 ^ i) | i <- [0 .. width - 1]]
  let carrySegment = zip carry [2 ^ i | i <- [width .. width * 2 - 1]]
  let outputSegment = [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]
  writeMul (fromInteger a, []) (0, bs) (0, outputSegment <> carrySegment)
compileMulU width out (Left a) (Right b) = do
  carry <- replicateM width (B <$> freshRefB)
  let as = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
  let carrySegment = zip carry [2 ^ i | i <- [width .. width * 2 - 1]]
  let outputSegment = [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]
  writeMul (0, as) (fromInteger b, []) (0, outputSegment <> carrySegment)
compileMulU width out (Left a) (Left b) = do
  carry <- replicateM width (B <$> freshRefB)

  let as = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
  let bs = [(B (RefUBit width b i), 2 ^ i) | i <- [0 .. width - 1]]
  let carrySegment = zip carry [2 ^ i | i <- [width .. width * 2 - 1]]
  let outputSegment = [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]

  writeMul (0, as) (0, bs) (0, outputSegment <> carrySegment)

compileMulU2 :: (GaloisField n, Integral n) => Int -> RefU -> Either RefU Integer -> Either RefU Integer -> M n ()
compileMulU2 width out (Right a) (Right b) = do
  let val = a * b
  writeValU (width * 2) out val
compileMulU2 width out (Right a) (Left b) = do
  let bs = [(B (RefUBit width b i), 2 ^ i) | i <- [0 .. width - 1]]
  let outputBits = [(B (RefUBit (width * 2) out i), 2 ^ i) | i <- [0 .. width * 2 - 1]]
  writeMul (fromInteger a, []) (0, bs) (0, outputBits)
compileMulU2 width out (Left a) (Right b) = do
  let as = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
  let outputBits = [(B (RefUBit (width * 2) out i), 2 ^ i) | i <- [0 .. width * 2 - 1]]
  writeMul (0, as) (fromInteger b, []) (0, outputBits)
compileMulU2 width out (Left a) (Left b) = do
  let as = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
  let bs = [(B (RefUBit width b i), 2 ^ i) | i <- [0 .. width - 1]]
  let outputBits = [(B (RefUBit (width * 2) out i), 2 ^ i) | i <- [0 .. width * 2 - 1]]
  writeMul (0, as) (0, bs) (0, outputBits)

-- | Conditional
--  out = p * x + (1 - p) * y
--      =>
--  out = p * x + y - p * y
--      =>
--  (out - y) = p * (x - y)
compileIfF :: (GaloisField n, Integral n) => Either RefB Bool -> LC n -> LC n -> M n (LC n)
compileIfF (Right True) x _ = return x
compileIfF (Right False) _ y = return y
compileIfF (Left p) (Constant x) (Constant y) = do
  if x == y
    then return $ Constant x
    else do
      out <- freshRefF
      -- (x - y) * p - out + y = 0
      let result = 1 @ F out
      writeAddWithLC $ (x - y) @ B p <> result <> Constant y
      return result
compileIfF (Left p) (Constant x) (Polynomial y) = do
  out <- freshRefF
  -- p * (x - y) = (out - y)
  let result = 1 @ F out
  writeMulWithLC
    (1 @ B p) -- p
    (Constant x <> neg (Polynomial y)) -- (x - y)
    (result <> neg (Polynomial y)) -- (out - y)
  return result
compileIfF (Left p) (Polynomial x) (Constant y) = do
  out <- freshRefF
  -- p * (x - y) = (out - y)
  let result = 1 @ F out
  writeMulWithLC
    (1 @ B p) -- p
    (Polynomial x <> neg (Constant y)) -- (x - y)
    (result <> neg (Constant y)) -- (out - y)
  return result
compileIfF (Left p) (Polynomial x) (Polynomial y) = do
  out <- freshRefF
  -- p * (x - y) = out - y
  let result = 1 @ F out
  writeMulWithLC
    (1 @ B p) -- p
    (Polynomial x <> neg (Polynomial y)) -- (x - y)
    (result <> neg (Polynomial y)) -- (out - y)
  return result

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

-- | Division with remainder on UInts
--    1. dividend = divisor * quotient + remainder
--    2. 0 ≤ remainder < divisor
--    3. 0 < divisor
assertDivModU :: (GaloisField n, Integral n) => Width -> ExprU n -> ExprU n -> ExprU n -> ExprU n -> M n ()
assertDivModU width dividend divisor quotient remainder = do
  --    dividend = divisor * quotient + remainder
  --  =>
  --    divisor * quotient = dividend - remainder
  remainderRef <- wireU remainder
  divisorRef <- wireU divisor
  quotientRef <- wireU quotient
  dividendRef <- wireU dividend

  productDQ <- freshRefU width
  compileMulU width productDQ divisorRef quotientRef
  UInt.compileSubU width productDQ dividendRef remainderRef

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
  UInt.assertLTE width a (c - 1)

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
  UInt.assertGTE width a (c + 1)

-- | Fast exponentiation on field
fastExp :: (GaloisField n, Integral n) => LC n -> n -> Integer -> M n (LC n)
fastExp _ acc 0 = return $ Constant acc
fastExp (Constant base) acc e = return $ Constant $ (base ^ e) * acc
fastExp (Polynomial base) acc e =
  let (q, r) = e `divMod` 2
   in if r == 1
        then do
          result <- fastExp (Polynomial base) acc (e - 1)
          mul result (Polynomial base)
        else do
          result <- fastExp (Polynomial base) acc q
          mul result result
  where
    -- \| Compute the multiplication of two variables
    mul :: (GaloisField n, Integral n) => LC n -> LC n -> M n (LC n)
    mul (Constant x) (Constant y) = return $ Constant (x * y)
    mul (Constant x) (Polynomial ys) = return $ fromEither $ PolyG.multiplyBy x ys
    mul (Polynomial xs) (Constant y) = return $ fromEither $ PolyG.multiplyBy y xs
    mul (Polynomial xs) (Polynomial ys) = do
      out <- freshRefF
      let result = 1 @ F out
      writeMulWithLC (Polynomial xs) (Polynomial ys) result
      return result

--------------------------------------------------------------------------------

-- | Temporary adapter for the LC type
handleLC :: (GaloisField n, Integral n) => Ref -> LC n -> M n ()
handleLC out (Constant val) = writeVal out val
handleLC out (Polynomial poly) = case PolyG.view poly of
  PolyG.Monomial 0 (x, 1) -> writeEq x out
  PolyG.Monomial c (x, a) -> writeAdd c [(out, -1), (x, a)]
  PolyG.Binomial c (x, a) (y, b) -> writeAdd c [(out, -1), (x, a), (y, b)]
  PolyG.Polynomial c xs -> writeAdd c $ (out, -1) : Map.toList xs

assertLC :: (GaloisField n, Integral n) => n -> LC n -> M n ()
assertLC val (Constant val') =
  if val == val'
    then return ()
    else throwError $ Error.ConflictingValuesF val val'
assertLC val (Polynomial poly) = case PolyG.view poly of
  PolyG.Monomial c (x, a) ->
    -- c + ax = val => x = (val - c) / a
    writeVal x ((val - c) / a)
  PolyG.Binomial c (x, a) (y, b) ->
    -- val = c + ax + by
    writeAdd (c - val) [(x, a), (y, b)]
  PolyG.Polynomial c xs ->
    -- val = c + xs...
    writeAdd (c - val) (Map.toList xs)

toLC :: (GaloisField n, Integral n) => ExprF n -> M n (LC n)
toLC (MulF (ValF m) (ValF n)) = return $ Constant (m * n)
toLC (MulF (VarF var) (ValF n)) = return $ n @ F (RefFX var)
toLC (MulF (VarFI var) (ValF n)) = return $ n @ F (RefFI var)
toLC (MulF (VarFO var) (ValF n)) = return $ n @ F (RefFX var)
toLC (MulF (ValF n) (VarF var)) = return $ n @ F (RefFX var)
toLC (MulF (ValF n) (VarFI var)) = return $ n @ F (RefFI var)
toLC (MulF (ValF n) (VarFO var)) = return $ n @ F (RefFO var)
toLC (MulF (ValF n) expr) = do
  result <- compileExprF expr
  case result of
    Constant val -> return $ Constant (val * n)
    Polynomial poly -> return $ scale n (Polynomial poly)
toLC (MulF expr (ValF n)) = do
  result <- compileExprF expr
  case result of
    Constant val -> return $ Constant (val * n)
    Polynomial poly -> return $ scale n (Polynomial poly)
toLC (ValF n) = return $ Constant n
toLC (VarF var) = return $ 1 @ F (RefFX var)
toLC (VarFI var) = return $ 1 @ F (RefFI var)
toLC (VarFO var) = return $ 1 @ F (RefFO var)
toLC expr = compileExprF expr