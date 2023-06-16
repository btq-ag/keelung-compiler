{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile (run) where

import Control.Arrow (left)
import Control.Monad
import Control.Monad.Except
-- import Keelung.Compiler.Syntax.FieldBits (FieldBits (..))

import Control.Monad.State
import Data.Bits (xor)
import Data.Bits qualified
import Data.Either (partitionEithers)
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Keelung (FieldType (..))
import Keelung.Compiler.Compile.Boolean qualified as Error.Boolean
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.LC
import Keelung.Compiler.Compile.Util
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintModule
import Keelung.Compiler.Error
import Keelung.Compiler.FieldInfo (FieldInfo (fieldTypeData, fieldWidth))
import Keelung.Compiler.Syntax.Internal
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
  assertLTE width x bound
compileSideEffect (AssertLT width value bound) = do
  x <- wireU value
  assertLT width x bound
compileSideEffect (AssertGTE width value bound) = do
  x <- wireU value
  assertGTE width x bound
compileSideEffect (AssertGT width value bound) = do
  x <- wireU value
  assertGT width x bound

-- | Compile the constraint 'out = x'.
compileAssertion :: (GaloisField n, Integral n) => Expr n -> M n ()
compileAssertion expr = case expr of
  ExprB (EqB x y) -> assertEqB x y
  ExprB (EqF x y) -> assertEqF x y
  ExprB (EqU x y) -> assertEqU x y
  -- rewriting `assert (x <= y)` width `assertLTE x y`
  ExprB (LTEU x (ValU width bound)) -> do
    x' <- wireU x
    assertLTE width x' (toInteger bound)
  ExprB (LTEU (ValU width bound) x) -> do
    x' <- wireU x
    assertGTE width x' (toInteger bound)
  ExprB (LTU x (ValU width bound)) -> do
    x' <- wireU x
    assertLT width x' (toInteger bound)
  ExprB (LTU (ValU width bound) x) -> do
    x' <- wireU x
    assertGT width x' (toInteger bound)
  ExprB (GTEU x (ValU width bound)) -> do
    x' <- wireU x
    assertGTE width x' (toInteger bound)
  ExprB (GTEU (ValU width bound) x) -> do
    x' <- wireU x
    assertLTE width x' (toInteger bound)
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
    compileAddU w out vars (sum constants)
  MulU w x y -> do
    x' <- wireU x
    y' <- wireU y
    compileMulBig w out x' y'
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
    assertLTE w (Left nRef) p
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

--------------------------------------------------------------------------------

-- Seq.fromList [(B carryVar, 2 ^ (i :: Int)) | (i, carryVar) <- zip [0 ..] previousCarries]

-- | We can add multiple limbs at once by piling them up.
--   But there's a limit to how many limbs we can pile up in one stack.
--   There higher we pile them up, the more space we need to store the carry.
--   We need to reserve at least 1 bit for the non-carry part of the limb.
-- determineMaxHeight :: Width -> Integer
-- determineMaxHeight fieldWidth = 2 ^ (fieldWidth - 2) -- 1 bit for non-carry, 1 bit useless

-- writeLimbVal :: (GaloisField n, Integral n) => Limb -> Integer -> M n (Maybe Limb)
-- writeLimbVal limb val = do
--   let range = [limbOffset limb .. limbOffset limb + limbWidth limb - 1]
--   forM_ range $ \i -> do
--     let bit = Data.Bits.testBit val i
--     writeValB (RefUBit (limbRefWidth limb) (limbRef limb) i) bit
--   return Nothing

-- -- | This function takes a pile of limbs and adds them together.
-- --   Takes:
-- --      1. an pre-allocated limb for storing the output
-- --      2. a pile of limbs
-- --      3. a constant (to be added to the result)
-- --   and returns:
-- --      1. a limb for representing the carry of the addition
-- --
-- --   NOTE: The number of limbs must not exceed the maximum height allowed.
-- addLimitedLimbs :: (GaloisField n, Integral n) => Limb -> [Limb] -> Integer -> M n [Limb]
-- addLimitedLimbs out [] constant = do
--   let range = [limbOffset out .. limbOffset out + limbWidth out - 1]
--   forM_ range $ \i -> do
--     let bit = Data.Bits.testBit constant i
--     writeValB (RefUBit (limbRefWidth out) (limbRef out) i) bit
--   return []
-- addLimitedLimbs out limbs constant = do
--   fieldWidth <- gets cmFieldWidth
--   let carryWidth = ceiling (logBase 2 (fromIntegral (length limbs) + if constant == 0 then 0 else 1) :: Double)
--   let range = [0 .. limbWidth out - 1]
--   let limbBits =
--         concat
--           [ [ (B (RefUBit (limbRefWidth limb) (limbRef limb) (limbOffset limb + i)), if limbSign limb then 2 ^ i else -(2 ^ i))
--               | i <- range
--             ]
--             | limb <- limbs
--           ]
--   -- for each negative operand, we compensate by adding 2^width
--   let constantSegment = sum [(if Data.Bits.testBit constant (limbOffset out + i) then 1 else 0) * (2 ^ i) | i <- range]
--   let numberOfNegativeOperand = length $ filter (not . limbSign) limbs
--   let compensatedConstant = constantSegment + 2 ^ limbRefWidth out * fromIntegral numberOfNegativeOperand
--   let resultBits = [(B (RefUBit (limbRefWidth out) (limbRef out) (limbOffset out + i)), -(2 ^ i)) | i <- range]

--   -- carry limb
--   carryRefU <- freshRefU carryWidth
--   let carryLimb = Limb carryRefU carryWidth (limbRefWidth out) 0 True
--   let carryBits = [(B (RefUBit (limbRefWidth out) carryRefU (limbOffset out + i)), -(2 ^ (limbWidth out + i))) | i <- [1 .. carryWidth] ]

--   writeAdd (fromInteger compensatedConstant) $ limbBits <> carryBits <> resultBits
--   return [carryLimb]

data Limb = Limb
  { -- | Which RefU this limb belongs to
    limbRef :: RefU,
    -- | How wide this limb is
    limbWidth :: Width,
    -- | The offset of this limb
    limbOffset :: Int,
    -- | True if this limb is positive, False if negative
    limbSign :: Bool
  }
  deriving (Show)

allocLimb :: (GaloisField n, Integral n) => Width -> Int -> Bool -> M n Limb
allocLimb w offset sign = do
  refU <- freshRefU w
  mapM_ addBooleanConstraint [RefUBit w refU i | i <- [0 .. w - 1]]
  return $
    Limb
      { limbRef = refU,
        limbWidth = w,
        limbOffset = offset,
        limbSign = sign
      }

-- | Given the UInt width, limb offset, and a limb, construct a sequence of bits.
toBits :: (GaloisField n, Integral n) => Int -> Int -> Bool -> Limb -> Seq (Ref, n)
toBits width powerOffset dontFlip limb =
  Seq.fromFunction
    (limbWidth limb)
    ( \i ->
        ( B (RefUBit width (limbRef limb) (limbOffset limb + i)),
          if not (limbSign limb `xor` dontFlip)
            then 2 ^ (powerOffset + i :: Int)
            else -(2 ^ (powerOffset + i :: Int))
        )
    )

compileAddU :: (GaloisField n, Integral n) => Width -> RefU -> [(RefU, Bool)] -> Integer -> M n ()
compileAddU width out [] constant = do
  -- constants only
  fieldWidth <- gets cmFieldWidth
  let carryWidth = 0 -- no carry needed
  let limbWidth = fieldWidth - 1 - carryWidth
  mapM_ (go limbWidth) [0, limbWidth .. width - 1]
  where
    go :: (GaloisField n, Integral n) => Int -> Int -> M n ()
    go limbWidth limbStart = do
      let range = [limbStart .. (limbStart + limbWidth - 1) `min` (width - 1)]
      forM_ range $ \i -> do
        let bit = Data.Bits.testBit constant i
        writeValB (RefUBit width out i) bit
compileAddU width out vars constant = do
  fieldWidth <- gets cmFieldWidth
  fieldInfo <- gets cmField
  -- for each negative operand, we compensate by adding 2^width
  let numberOfNegativeOperand = length $ filter (not . snd) vars
  -- we need some extra bits for carry when adding UInts
  let expectedCarryWidth = ceiling (logBase 2 (fromIntegral (length vars) + if constant == 0 then 0 else 1) :: Double)
  let limbWidth = (fieldWidth - 1 - expectedCarryWidth) `max` 1
  let carryWidth = fieldWidth - 1 - limbWidth
  -- for each negative operand, we compensate by adding 2^width
  -- let compensatedConstant = constant + 2 ^ width * fromIntegral numberOfNegativeOperand


  -- let added = sum (map (\start -> let currentLimbWidth = limbWidth `min` (width - start) in 2 ^ currentLimbWidth) [0, limbWidth .. width - 1])
  -- let buffed = (2 ^ width * fromIntegral numberOfNegativeOperand) - added
  -- traceShowM (added, buffed)

  maxHeight <- maxHeightAllowed
  case fieldTypeData fieldInfo of
    Binary _ -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 2 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 3 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    _ -> do
      let ranges =
            map
              ( \start ->
                  let currentLimbWidth = limbWidth `min` (width - start)
                      resultLimb = Limb out currentLimbWidth start True
                      operandLimbs = [Limb var currentLimbWidth start sign | (var, sign) <- vars]
                      constantSegment = sum [(if Data.Bits.testBit constant (start + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidth - 1]]
                      compensatedConstant = constantSegment + 2 ^ currentLimbWidth * fromIntegral numberOfNegativeOperand
                   in (start, currentLimbWidth, resultLimb, operandLimbs, compensatedConstant)
              )
              [0, limbWidth .. width - 1]
      foldM_ (addLimbs width maxHeight carryWidth) [] ranges

-- | Maximum number of limbs allowed to be added at once
maxHeightAllowed :: M n Int
maxHeightAllowed = do
  w <- gets (fieldWidth . cmField)
  if w <= 10
    then return (2 ^ (w - 2))
    else return 256

addLimbs :: (GaloisField n, Integral n) => Width -> Int -> Int -> [Limb] -> (Int, Int, Limb, [Limb], Integer) -> M n [Limb]
addLimbs width maxHeight carryWidth previousCarries (limbStart, currentLimbWidth, resultLimb, limbs, constant) = do
  addLimbs' width maxHeight carryWidth resultLimb (limbStart, currentLimbWidth, previousCarries <> limbs, constant)

addLimbs' :: (GaloisField n, Integral n) => Width -> Int -> Int -> Limb -> (Int, Int, [Limb], Integer) -> M n [Limb]
addLimbs' width maxHeight carryWidth out (limbStart, currentLimbWidth, limbs, constant) = do
  let (currentBatch, nextBatch) = splitAt (maxHeight - if constant == 0 then 0 else 1) limbs
  if null nextBatch
    then do
      addLimitedLimbs width carryWidth [] (limbStart, currentLimbWidth, out, currentBatch, constant)
    else do
      tempResultLimb <- allocLimb currentLimbWidth limbStart True
      x <- addLimitedLimbs width carryWidth [] (limbStart, currentLimbWidth, tempResultLimb, currentBatch, constant)
      xs <- addLimbs' width maxHeight carryWidth out (limbStart, currentLimbWidth, tempResultLimb : nextBatch, 0)
      return $ x <> xs

addLimitedLimbs :: (GaloisField n, Integral n) => Width -> Int -> [Limb] -> (Int, Int, Limb, [Limb], Integer) -> M n [Limb]
addLimitedLimbs width carryWidth previousCarries (limbStart, currentLimbWidth, resultLimb, limbs, compensatedConstant) = do
  carryLimb <- allocLimb carryWidth (limbStart + currentLimbWidth) True
  -- limbs + previousCarryLimb = resultLimb + carryLimb
  writeAddWithSeq (fromInteger compensatedConstant) $
    mconcat (map (toBits width 0 True) previousCarries)
      <> mconcat (map (toBits width 0 True) limbs)
      <> toBits width 0 False resultLimb
      <> toBits width currentLimbWidth False carryLimb -- multiply carryBits by `2^currentLimbWidth` and negate it
  return [carryLimb]

compileSubU :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU Integer -> Either RefU Integer -> M n ()
compileSubU width out (Right a) (Right b) = compileAddU width out [] (a - b)
compileSubU width out (Right a) (Left b) = compileAddU width out [(b, False)] a
compileSubU width out (Left a) (Right b) = compileAddU width out [(a, True)] (-b)
compileSubU width out (Left a) (Left b) = compileAddU width out [(a, True), (b, False)] 0

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

-- assume that each number has been divided into L w-bit limbs
-- multiplying two numbers will result in L^2 2w-bit limbs
--
--                          a1 a2 a3
-- x                        b1 b2 b3
-- ------------------------------------------
--                             a3*b3
--                          a2*b3
--                       a1*b3
--                          a3*b2
--                       a2*b2
--                    a1*b2
--                       a3*b1
--                    a2*b1
--                 a1*b1
-- ------------------------------------------
--
-- the maximum number of operands when adding these 2w-bit limbs is 2L (with carry from the previous limb)
-- so each limb would need to be at least ceiling(log2(2L)) bits wide

-- compileMulBigCV :: (GaloisField n, Integral n) => Int -> RefU -> Integer -> RefU -> M n ()
-- compileMulBigCV width out a b = do
--   -- mulpliplying two w-bit numbers will result in a 2w-bit number
--   carries <- replicateM width freshRefB
--   mapM_ addBooleanConstraint carries

compileMulBig :: (GaloisField n, Integral n) => Int -> RefU -> Either RefU Integer -> Either RefU Integer -> M n ()
compileMulBig width out (Right a) (Right b) = do
  let val = a * b
  writeValU width out val
compileMulBig width out (Right a) (Left b) = do
  carry <- replicateM width (B <$> freshRefB)
  let bs = [(B (RefUBit width b i), 2 ^ i) | i <- [0 .. width - 1]]
  let carrySegment = zip carry [2 ^ i | i <- [width .. width * 2 - 1]]
  let outputSegment = [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]
  writeMul (fromInteger a, []) (0, bs) (0, outputSegment <> carrySegment)
compileMulBig width out (Left a) (Right b) = compileMulBig width out (Right b) (Left a)
compileMulBig width out (Left a) (Left b) = do
  carry <- replicateM width (B <$> freshRefB)

  let as = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
  let bs = [(B (RefUBit width b i), 2 ^ i) | i <- [0 .. width - 1]]
  let carrySegment = zip carry [2 ^ i | i <- [width .. width * 2 - 1]]
  let outputSegment = [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]

  writeMul (0, as) (0, bs) (0, outputSegment <> carrySegment)

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
  compileSubU width productDQ dividendRef remainderRef

  -- 0 ≤ remainder < divisor
  compileAssertion $ ExprB (LTU remainder divisor)
  -- 0 < divisor
  assertGT width divisorRef 0
  -- add hint for DivMod
  addDivModHint width dividendRef divisorRef quotientRef remainderRef

--------------------------------------------------------------------------------

-- | Assert that a UInt is less than or equal to some constant
-- reference doc: A.3.2.2 Range Check https://zips.z.cash/protocol/protocol.pdf
assertLTE :: (GaloisField n, Integral n) => Width -> Either RefU Integer -> Integer -> M n ()
assertLTE _ (Right a) bound = if fromIntegral a <= bound then return () else throwError $ Error.AssertComparisonError (toInteger a) LT (succ bound)
assertLTE width (Left a) bound
  | bound < 0 = throwError $ Error.AssertLTEBoundTooSmallError bound
  | bound >= 2 ^ width - 1 = throwError $ Error.AssertLTEBoundTooLargeError bound width
  | bound == 0 = do
      -- there's only 1 possible value for `a`, which is `0`
      -- let bits = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
      -- writeAdd 0 bits
      writeValU width a 0
  | bound == 1 = do
      -- there are 2 possible values for `a`, which are `0` and `1`
      -- we can use these 2 values as the only roots of the following multiplicative polynomial
      let bits = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
      writeMul (0, bits) (-1, bits) (0, [])
  | bound == 2 = do
      -- there are 3 possible values for `a`, which are `0`, `1` and `2`
      -- we can use these 3 values as the only roots of the following 2 multiplicative polynomial
      let bits = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
      temp <- freshRefF
      writeMul (0, bits) (-1, bits) (0, [(F temp, 1)])
      writeMul (0, [(F temp, 1)]) (-2, bits) (0, [])
  | otherwise = do
      -- because we don't have to execute the `go` function for trailing ones of `c`
      -- we can limit the range of bits of c from `[width-1, width-2 .. 0]` to `[width-1, width-2 .. countTrailingOnes]`
      foldM_ (go a) Nothing [width - 1, width - 2 .. (width - 2) `min` countTrailingOnes]
  where
    -- for counting the number of trailing ones of `c`
    countTrailingOnes :: Int
    countTrailingOnes =
      fst $
        foldl
          ( \(count, keepCounting) i ->
              if keepCounting && Data.Bits.testBit bound i then (count + 1, True) else (count, False)
          )
          (0, True)
          [0 .. width - 1]

    go :: (GaloisField n, Integral n) => RefU -> Maybe Ref -> Int -> M n (Maybe Ref)
    go ref Nothing i =
      let aBit = RefUBit width ref i
       in -- have not found the first bit in 'c' that is 1 yet
          if Data.Bits.testBit bound i
            then do
              return $ Just (B aBit) -- when found, return a[i]
            else do
              -- a[i] = 0
              writeValB aBit False
              return Nothing -- otherwise, continue searching
    go ref (Just acc) i =
      let aBit = B (RefUBit width ref i)
       in if Data.Bits.testBit bound i
            then do
              -- constraint for the next accumulator
              -- acc * a[i] = acc'
              -- such that if a[i] = 1
              --    then acc' = acc
              --    else acc' = 0
              acc' <- freshRefF
              writeMul (0, [(acc, 1)]) (0, [(aBit, 1)]) (0, [(F acc', 1)])
              return $ Just (F acc')
            else do
              -- constraint on a[i]
              -- (1 - acc - a[i]) * a[i] = 0
              -- such that if acc = 0 then a[i] = 0 or 1 (don't care)
              --           if acc = 1 then a[i] = 0
              writeMul (1, [(acc, -1), (aBit, -1)]) (0, [(aBit, 1)]) (0, [])
              -- pass down the accumulator
              return $ Just acc

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

-- | Assert that a UInt is greater than or equal to some constant
assertGTE :: (GaloisField n, Integral n) => Width -> Either RefU Integer -> Integer -> M n ()
assertGTE _ (Right a) c = if fromIntegral a >= c then return () else throwError $ Error.AssertComparisonError (succ (toInteger a)) GT c
assertGTE width (Left a) bound
  | bound < 1 = throwError $ Error.AssertGTEBoundTooSmallError bound
  | bound >= 2 ^ width = throwError $ Error.AssertGTEBoundTooLargeError bound width
  | bound == 2 ^ width - 1 = do
      -- there's only 1 possible value for `a`, which is `2^width - 1`
      let bits = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
      writeAdd (1 - 2 ^ width) bits
  | bound == 2 ^ width - 2 = do
      -- there's only 2 possible value for `a`, which is `2^width - 1` or `2^width - 2`
      -- we can use these 2 values as the only roots of the following multiplicative polynomial
      let bits = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
      writeMul (1 - 2 ^ width, bits) (2 - 2 ^ width, bits) (0, [])
  | bound == 2 ^ width - 3 = do
      -- there's only 3 possible value for `a`, which is `2^width - 1`, `2^width - 2` or `2^width - 3`
      -- we can use these 3 values as the only roots of the following 2 multiplicative polynomial
      let bits = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
      temp <- freshRefF
      writeMul (1 - 2 ^ width, bits) (2 - 2 ^ width, bits) (0, [(F temp, 1)])
      writeMul (0, [(F temp, 1)]) (3 - 2 ^ width, bits) (0, [])
  | bound == 1 = do
      -- a >= 1 => a > 0 => a is not zero
      -- there exists a number m such that the product of a and m is 1
      m <- freshRefF
      let bits = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
      writeMul (0, bits) (0, [(F m, 1)]) (1, [])
  | otherwise = do
      flag <- freshRefF
      writeValF flag 1
      -- because we don't have to execute the `go` function for trailing zeros of `bound`
      -- we can limit the range of bits of c from `[width-1, width-2 .. 0]` to `[width-1, width-2 .. countTrailingZeros]`
      foldM_ (go a) (F flag) [width - 1, width - 2 .. (width - 2) `min` countTrailingZeros]
  where
    -- for counting the number of trailing zeros of `bound`
    countTrailingZeros :: Int
    countTrailingZeros =
      fst $
        foldl
          ( \(count, keepCounting) i ->
              if keepCounting && not (Data.Bits.testBit bound i) then (count + 1, True) else (count, False)
          )
          (0, True)
          [0 .. width - 1]

    go :: (GaloisField n, Integral n) => RefU -> Ref -> Int -> M n Ref
    go ref flag i =
      let aBit = RefUBit width ref i
          bBit = Data.Bits.testBit bound i
       in if bBit
            then do
              -- constraint on bit
              -- (flag + bit - 1) * bit = flag
              -- such that if flag = 0 then bit = 0 or 1 (don't care)
              --           if flag = 1 then bit = 1
              writeMul (-1, [(B aBit, 1), (flag, 1)]) (0, [(B aBit, 1)]) (0, [(flag, 1)])
              return flag
            else do
              flag' <- freshRefF
              -- flag' := flag * (1 - bit)
              writeMul (0, [(flag, 1)]) (1, [(B aBit, -1)]) (0, [(F flag', 1)])
              return (F flag')

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