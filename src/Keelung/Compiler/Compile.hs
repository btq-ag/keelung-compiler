{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile (run) where

import Control.Arrow (left)
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Bits qualified
-- import Keelung.Compiler.Syntax.FieldBits (FieldBits (..))

import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq (..))
import Keelung.Compiler.Compile.Boolean qualified as Compile.Boolean
import Keelung.Compiler.Compile.Error qualified as Compile
import Keelung.Compiler.Compile.LC
import Keelung.Compiler.Compile.Util
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintModule
import Keelung.Compiler.Error
import Keelung.Compiler.Syntax.FieldBits qualified as FieldBits
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Field (FieldType)
import Keelung.Syntax (widthOf)
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

-- | Compile an untyped expression to a constraint system
run :: (GaloisField n, Integral n) => (FieldType, Integer, Integer) -> Internal n -> Either (Error n) (ConstraintModule n)
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
  x <- wireU' value
  assertLTE2 width x bound
compileSideEffect (AssertLT width value bound) = assertLT width value bound
compileSideEffect (AssertGTE width value bound) = assertGTE width value bound
compileSideEffect (AssertGT width value bound) = assertGT width value bound

-- | Compile the constraint 'out = x'.
compileAssertion :: (GaloisField n, Integral n) => Expr n -> M n ()
compileAssertion expr = case expr of
  ExprB (EqB x y) -> assertEqB x y
  ExprB (EqF x y) -> assertEqF x y
  ExprB (EqU x y) -> assertEqU x y
  -- rewriting `assert (x <= y)` width `assertLTE x y`
  ExprB (LTEU x (ValU width bound)) -> do
    x' <- wireU' x
    assertLTE2 width x' (toInteger bound)
  ExprB (LTEU (ValU width bound) x) -> assertGTE width x (toInteger bound)
  ExprB (LTU x (ValU width bound)) -> assertLT width x (toInteger bound)
  ExprB (LTU (ValU width bound) x) -> assertGT width x (toInteger bound)
  ExprB (GTEU x (ValU width bound)) -> assertGTE width x (toInteger bound)
  ExprB (GTEU (ValU width bound) x) -> do
    x' <- wireU' x
    assertLTE2 width x' (toInteger bound)
  ExprB (GTU x (ValU width bound)) -> assertGT width x (toInteger bound)
  ExprB (GTU (ValU width bound) x) -> assertLT width x (toInteger bound)
  ExprB x -> do
    -- out <- freshRefB
    result <- compileExprB x
    case result of
      Left var -> writeValB var True
      Right True -> return ()
      Right val -> throwError $ Compile.ConflictingValuesB True val
  ExprF x -> do
    result <- compileExprF x
    assertLC 1 result
  ExprU x -> do
    out <- freshRefU (widthOf x)
    compileExprU out x
    writeValU out 1

-- | Assert that two Boolean expressions are equal
assertEqB :: (GaloisField n, Integral n) => ExprB n -> ExprB n -> M n ()
assertEqB (ValB a) (ValB b) = when (a /= b) $ throwError $ Compile.ConflictingValuesB a b
assertEqB (ValB a) (VarB b) = writeValB (RefBX b) a
assertEqB (ValB a) (VarBO b) = writeValB (RefBO b) a
assertEqB (ValB a) (VarBI b) = writeValB (RefBI b) a
assertEqB (ValB a) (VarBP b) = writeValB (RefBP b) a
assertEqB (ValB a) b = do
  result <- compileExprB b
  case result of
    Left var -> writeValB var a
    Right val -> when (a /= val) $ throwError $ Compile.ConflictingValuesB a val
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
    (Right valA, Right valB) -> when (valA /= valB) $ throwError $ Compile.ConflictingValuesB valA valB

-- | Assert that two Field expressions are equal
assertEqF :: (GaloisField n, Integral n) => ExprF n -> ExprF n -> M n ()
assertEqF (ValF a) (ValF b) = when (a /= b) $ throwError $ Compile.ConflictingValuesF a b
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
assertEqU (ValU _ a) (ValU _ b) = when (a /= b) $ throwError $ Compile.ConflictingValuesU a b
assertEqU (ValU w a) (VarU _ b) = writeValU (RefUX w b) a
assertEqU (ValU w a) (VarUO _ b) = writeValU (RefUO w b) a
assertEqU (ValU w a) (VarUI _ b) = writeValU (RefUI w b) a
assertEqU (ValU w a) (VarUP _ b) = writeValU (RefUP w b) a
assertEqU (ValU w a) b = do
  out <- freshRefU w
  compileExprU out b
  writeValU out a
assertEqU (VarU w a) (ValU _ b) = writeValU (RefUX w a) b
assertEqU (VarU w a) (VarU _ b) = writeEqU (RefUX w a) (RefUX w b)
assertEqU (VarU w a) (VarUO _ b) = writeEqU (RefUX w a) (RefUO w b)
assertEqU (VarU w a) (VarUI _ b) = writeEqU (RefUX w a) (RefUI w b)
assertEqU (VarU w a) (VarUP _ b) = writeEqU (RefUX w a) (RefUP w b)
assertEqU (VarU w a) b = do
  out <- freshRefU w
  compileExprU out b
  writeEqU (RefUX w a) out
assertEqU (VarUO w a) (ValU _ b) = writeValU (RefUO w a) b
assertEqU (VarUO w a) (VarU _ b) = writeEqU (RefUO w a) (RefUX w b)
assertEqU (VarUO w a) (VarUO _ b) = writeEqU (RefUO w a) (RefUO w b)
assertEqU (VarUO w a) (VarUI _ b) = writeEqU (RefUO w a) (RefUI w b)
assertEqU (VarUO w a) (VarUP _ b) = writeEqU (RefUO w a) (RefUP w b)
assertEqU (VarUO w a) b = do
  out <- freshRefU w
  compileExprU out b
  writeEqU (RefUO w a) out
assertEqU (VarUI w a) (ValU _ b) = writeValU (RefUI w a) b
assertEqU (VarUI w a) (VarU _ b) = writeEqU (RefUI w a) (RefUX w b)
assertEqU (VarUI w a) (VarUO _ b) = writeEqU (RefUI w a) (RefUO w b)
assertEqU (VarUI w a) (VarUI _ b) = writeEqU (RefUI w a) (RefUI w b)
assertEqU (VarUI w a) (VarUP _ b) = writeEqU (RefUI w a) (RefUP w b)
assertEqU (VarUI w a) b = do
  out <- freshRefU w
  compileExprU out b
  writeEqU (RefUI w a) out
assertEqU (VarUP w a) (ValU _ b) = writeValU (RefUP w a) b
assertEqU (VarUP w a) (VarU _ b) = writeEqU (RefUP w a) (RefUX w b)
assertEqU (VarUP w a) (VarUO _ b) = writeEqU (RefUP w a) (RefUO w b)
assertEqU (VarUP w a) (VarUI _ b) = writeEqU (RefUP w a) (RefUI w b)
assertEqU (VarUP w a) (VarUP _ b) = writeEqU (RefUP w a) (RefUP w b)
assertEqU (VarUP w a) b = do
  out <- freshRefU w
  compileExprU out b
  writeEqU (RefUP w a) out
assertEqU a b = do
  let width = widthOf a
  a' <- freshRefU width
  b' <- freshRefU width
  compileExprU a' a
  compileExprU b' b
  writeEqU a' b'

----------------------------------------------------------------

freshExprU :: Width -> M n (ExprU n)
freshExprU width = do
  counters <- gets cmCounters
  let index = getCount counters (Intermediate, ReadUInt width)
  modifyCounter $ addCount (Intermediate, WriteUInt width) 1
  return $ VarU width index

----------------------------------------------------------------

compileExprB :: (GaloisField n, Integral n) => ExprB n -> M n (Either RefB Bool)
compileExprB = Compile.Boolean.compileExprB wireU' compileExprF

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
  ValU width val -> do
    forM_ [0 .. width - 1] $ \i -> do
      writeValB (RefUBit width out i) (FieldBits.testBit' val i)
  VarU width var -> writeEqU out (RefUX width var)
  VarUO width var -> writeEqU out (RefUX width var) -- out = var
  VarUI width var -> do
    let ref = RefUI width var
    -- constraint for UInt : out = ref
    writeEqU out ref
    -- constraints for BinRep of UInt
    forM_ [0 .. width - 1] $ \i -> do
      writeEqB (RefUBit width out i) (RefUBit width ref i) -- out[i] = ref[i]
  VarUP width var -> do
    let ref = RefUP width var
    -- constraint for UInt : out = ref
    writeEqU out ref
    -- constraints for BinRep of UInt
    forM_ [0 .. width - 1] $ \i -> do
      writeEqB (RefUBit width out i) (RefUBit width ref i) -- out[i] = ref[i]
  SubU w x y -> do
    x' <- wireU' x
    y' <- wireU' y
    compileSubU w out x' y'
  AddU w x y -> do
    x' <- wireU' x
    y' <- wireU' y
    compileAddU w out x' y'
  MulU w x y -> do
    x' <- wireU' x
    y' <- wireU' y
    compileMulU w out x' y'
  MMIU w a p -> do
    -- See: https://github.com/btq-ag/keelung-compiler/issues/14
    -- 1. a * a⁻¹ = np + 1
    -- 2. n ≤ ⌈log₂p⌉
    a' <- wireU a
    -- n <- freshExprU w
    nRef <- freshRefU w
    let ceilingLg2P = ceiling (logBase 2 (fromInteger p) :: Double)
    writeMul (0, [(U a', 1)]) (0, [(U out, 1)]) (1, [(U nRef, fromInteger p)])
    addModInvHint a' nRef p
    assertLTE2 w (Left nRef) ceilingLg2P
  AndU w x y xs -> do
    forM_ [0 .. w - 1] $ \i -> do
      result <- compileExprB (AndB (BitU x i) (BitU y i) (fmap (`BitU` i) xs))
      case result of
        Left var -> writeEqB (RefUBit w out i) var
        Right val -> writeValB (RefUBit w out i) val
  OrU w x y xs -> do
    forM_ [0 .. w - 1] $ \i -> do
      result <- compileExprB (OrB (BitU x i) (BitU y i) (fmap (`BitU` i) xs))
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
  IfU width p x y -> do
    p' <- compileExprB p
    x' <- wireU' x
    y' <- wireU' y
    result <- compileIfU width p' x' y'
    case result of
      Left var -> writeEqU out var
      Right val -> writeValU out val
  RoLU w n x -> do
    result <- wireU' x
    case result of
      Left var -> do
        forM_ [0 .. w - 1] $ \i -> do
          let i' = (i - n) `mod` w
          writeEqB (RefUBit w out i) (RefUBit w var i') -- out[i] = x[i']
      Right val -> do
        forM_ [0 .. w - 1] $ \i -> do
          let i' = (i - n) `mod` w
          writeValB (RefUBit w out i) (FieldBits.testBit' val i') -- out[i] = val[i']
  ShLU w n x -> do
    x' <- wireU' x
    case compare n 0 of
      EQ -> case x' of
        Left var -> writeEqU out var
        Right val -> writeValU out val
      GT -> do
        -- fill lower bits with 0s
        forM_ [0 .. n - 1] $ \i -> do
          writeValB (RefUBit w out i) False -- out[i] = 0
          -- shift upper bits
        forM_ [n .. w - 1] $ \i -> do
          let i' = i - n
          case x' of
            Left var -> writeEqB (RefUBit w out i) (RefUBit w var i') -- out[i] = x'[i']
            Right val -> writeValB (RefUBit w out i) (FieldBits.testBit' val i') -- out[i] = x'[i']
      LT -> do
        -- shift lower bits
        forM_ [0 .. w + n - 1] $ \i -> do
          let i' = i - n
          case x' of
            Left var -> writeEqB (RefUBit w out i) (RefUBit w var i') -- out[i] = x'[i']
            Right val -> writeValB (RefUBit w out i) (FieldBits.testBit' val i') -- out[i] = x'[i']
            -- fill upper bits with 0s
        forM_ [w + n .. w - 1] $ \i -> do
          writeValB (RefUBit w out i) False -- out[i] = 0
  SetU w x j b -> do
    x' <- wireU' x
    b' <- wireB b
    forM_ [0 .. w - 1] $ \i -> do
      if i == j
        then writeEqB (RefUBit w out i) b' -- out[i] = b
        else do
          case x' of
            Left var -> writeEqB (RefUBit w out i) (RefUBit w var i) -- out[i] = x'[i]
            Right val -> writeValB (RefUBit w out i) (FieldBits.testBit' val i) -- out[i] = x'[i]
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

-- | If the expression is not already a variable, create a new variable
wireB :: (GaloisField n, Integral n) => ExprB n -> M n RefB
wireB (VarB ref) = return (RefBX ref)
wireB (VarBO ref) = return (RefBO ref)
wireB (VarBI ref) = return (RefBI ref)
wireB (VarBP ref) = return (RefBP ref)
wireB expr = do
  result <- compileExprB expr
  case result of
    Left var -> return var
    Right val -> do
      out <- freshRefB
      writeValB out val
      return out

wireU :: (GaloisField n, Integral n) => ExprU n -> M n RefU
wireU (VarU w ref) = return (RefUX w ref)
wireU (VarUO w ref) = return (RefUO w ref)
wireU (VarUI w ref) = return (RefUI w ref)
wireU (VarUP w ref) = return (RefUP w ref)
wireU expr = do
  out <- freshRefU (widthOf expr)
  compileExprU out expr
  return out

wireU' :: (GaloisField n, Integral n) => ExprU n -> M n (Either RefU n)
wireU' (ValU _ val) = return (Right val)
wireU' others = Left <$> wireU others

--------------------------------------------------------------------------------

-- | Encoding addition on UInts with multiple operands: O(1)
--      A       =          2ⁿAₙ₋₁ + ... + 2A₁ + A₀
--      B       =          2ⁿBₙ₋₁ + ... + 2B₁ + B₀
--      C       = 2ⁿ⁺¹Cₙ + 2ⁿCₙ₋₁ + ... + 2C₁ + C₀
--      Result  =          2ⁿCₙ₋₁ + ... + 2C₁ + C₀
--      C       = A + B
compileAddOrSubU :: (GaloisField n, Integral n) => Bool -> Width -> RefU -> Either RefU n -> Either RefU n -> M n ()
compileAddOrSubU isSub width out (Right a) (Right b) = do
  let val = if isSub then a - b else a + b
  forM_ [0 .. width - 1] $ \i -> do
    -- Cᵢ = outᵢ
    writeValB (RefUBit width out i) (FieldBits.testBit' val i)
compileAddOrSubU isSub width out (Right a) (Left b) = do
  carry <- freshRefB
  addBooleanConstraint carry
  let bs = [(B (RefUBit width b i), if isSub then -(2 ^ i) else 2 ^ i) | i <- [0 .. width - 1]]
  let carryAndResult = (B carry, -(2 ^ width)) : [(B (RefUBit width out i), -(2 ^ i)) | i <- [0 .. width - 1]]
  writeAdd a $ bs <> carryAndResult
-- c <- freshRefU (width + 1)
-- -- C = A + B
-- writeAdd a [(U b, if isSub then -1 else 1), (U c, -1)]
-- -- copying bits from C to 'out'
-- forM_ [0 .. width - 1] $ \i -> do
--   -- Cᵢ = outᵢ
--   writeEqB (RefUBit width c i) (RefUBit width out i)
compileAddOrSubU isSub width out (Left a) (Right b) = do
  carry <- freshRefB
  addBooleanConstraint carry
  let as = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
  let carryAndResult = (B carry, -(2 ^ width)) : [(B (RefUBit width out i), -(2 ^ i)) | i <- [0 .. width - 1]]
  writeAdd (if isSub then -b else b) $ as <> carryAndResult

-- c <- freshRefU (width + 1)
-- -- C = A + B
-- writeAdd (if isSub then -b else b) [(U a, 1), (U c, -1)]
-- -- copying bits from C to 'out'
-- forM_ [0 .. width - 1] $ \i -> do
--   -- Cᵢ = outᵢ
--   writeEqB (RefUBit width c i) (RefUBit width out i)
compileAddOrSubU isSub width out (Left a) (Left b) = do
  carry <- freshRefB
  addBooleanConstraint carry
  -- out + carry = A + B
  let as = [(B (RefUBit width a i), -(2 ^ i)) | i <- [0 .. width - 1]]
  let bs = [(B (RefUBit width b i), if isSub then 2 ^ i else -(2 ^ i)) | i <- [0 .. width - 1]]
  let carryAndResult = (B carry, 2 ^ width) : [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]

  writeAdd 0 $ as <> bs <> carryAndResult

-- addBinRepHint [(RefUBit width out 0, 4), (carry, 1)]

-- c <- freshRefU (width + 1)
-- -- C = A + B
-- writeAdd 0 [(U a, 1), (U b, if isSub then -1 else 1), (U c, -1)]
-- -- copying bits from C to 'out'
-- forM_ [0 .. width - 1] $ \i -> do
--   -- Cᵢ = outᵢ
--   writeEqB (RefUBit width c i) (RefUBit width out i)

compileAddU :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU n -> Either RefU n -> M n ()
compileAddU = compileAddOrSubU False

compileSubU :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU n -> Either RefU n -> M n ()
compileSubU = compileAddOrSubU True

-- | Encoding addition on UInts with multiple operands: O(2)
--      A       =   2ⁿAₙ₋₁ + ... + 2A₁ + A₀
--      B       =   2ⁿBₙ₋₁ + ... + 2B₁ + B₀
--      C       = 2²ⁿC₂ₙ₋₁ + ... + 2C₁ + C₀
--      Result  =   2ⁿCₙ₋₁ + ... + 2C₁ + C₀
compileMulU :: (GaloisField n, Integral n) => Int -> RefU -> Either RefU n -> Either RefU n -> M n ()
compileMulU width out (Right a) (Right b) = do
  let val = a * b
  forM_ [0 .. width - 1] $ \i -> do
    writeValB (RefUBit width out i) (FieldBits.testBit' val i)
compileMulU width out (Right a) (Left b) = do
  carry <- replicateM width (B <$> freshRefB)
  let bs = [(B (RefUBit width b i), 2 ^ i) | i <- [0 .. width - 1]]
  let carrySegment = zip carry [2 ^ i | i <- [width .. width * 2 - 1]]
  let outputSegment = [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]
  writeMul (a, []) (0, bs) (0, outputSegment <> carrySegment)

-- writeAdd 0 [(U b, -a), (U out, 1)]
compileMulU width out (Left a) (Right b) = do
  carry <- replicateM width (B <$> freshRefB)
  let as = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
  let carrySegment = zip carry [2 ^ i | i <- [width .. width * 2 - 1]]
  let outputSegment = [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]
  writeMul (0, as) (b, []) (0, outputSegment <> carrySegment)
-- writeAdd 0 [(U a, -b), (U out, 1)]
compileMulU width out (Left a) (Left b) = do
  carry <- replicateM width (B <$> freshRefB)

  let as = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
  let bs = [(B (RefUBit width b i), 2 ^ i) | i <- [0 .. width - 1]]
  let carrySegment = zip carry [2 ^ i | i <- [width .. width * 2 - 1]]
  let outputSegment = [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]

  writeMul (0, as) (0, bs) (0, outputSegment <> carrySegment)

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
compileIfU :: (GaloisField n, Integral n) => Width -> Either RefB Bool -> Either RefU n -> Either RefU n -> M n (Either RefU n)
compileIfU _ (Right True) x _ = return x
compileIfU _ (Right False) _ y = return y
compileIfU width (Left p) (Right x) (Right y) = do
  if x == y
    then return $ Right x
    else do
      out <- freshRefU width
      -- (x - y) * p - out + y = 0
      writeAdd y [(B p, x - y), (U out, -1)]
      return $ Left out
compileIfU width (Left p) (Right x) (Left y) = do
  out <- freshRefU width
  -- (out - y) = p * (x - y)
  writeMul
    (0, [(B p, 1)])
    (x, [(U y, -1)])
    (0, [(U y, -1), (U out, 1)])
  return $ Left out
compileIfU width (Left p) (Left x) (Right y) = do
  out <- freshRefU width
  -- (out - y) = p * (x - y)
  writeMul
    (0, [(B p, 1)])
    (-y, [(U x, 1)])
    (-y, [(U out, 1)])
  return $ Left out
compileIfU width (Left p) (Left x) (Left y) = do
  out <- freshRefU width
  -- (out - y) = p * (x - y)
  writeMul
    (0, [(B p, 1)])
    (0, [(U x, 1), (U y, -1)])
    (0, [(U y, -1), (U out, 1)])
  return $ Left out

--------------------------------------------------------------------------------

assertNotZeroU :: (GaloisField n, Integral n) => Width -> ExprU n -> M n ()
assertNotZeroU width expr = do
  ref <- wireU' expr
  -- introduce a new variable m, such that `expr * m = 1`
  m <- freshRefU width
  case ref of
    Left var -> do
      writeMul
        (0, [(U var, 1)])
        (0, [(U m, 1)])
        (1, [])
    Right 0 -> throwError $ Compile.ConflictingValuesU 1 0
    Right _ -> return ()

-- | Assert that x is less than or equal to y
--
-- TODO, replace with a more efficient implementation
--  as in A.3.2.2 Range check in https://zips.z.cash/protocol/protocol.pdf
-- assertLTEU :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> M n ()
-- assertLTEU width x y = do
--   --    x ≤ y
--   --  =>
--   --    0 ≤ y - x
--   --  that is, there exists a BinRep of y - x
--   difference <- freshRefU  width
--   compileSubU width difference y x
assertLTU :: (GaloisField n, Integral n) => Width -> Either RefU n -> Either RefU n -> M n ()
assertLTU width x y = do
  --    x < y
  --  =>
  --    0 < y - x
  --  that is, there exists a non-zero BinRep of y - x
  difference <- freshExprU width
  difference' <- wireU difference
  compileSubU width difference' y x
  assertNotZeroU width difference

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
  addDivModHint (Left dividendRef) (Left divisorRef) (Left quotientRef) (Left remainderRef)
  writeMul
    (0, [(U divisorRef, 1)])
    (0, [(U quotientRef, 1)])
    (0, [(U dividendRef, 1), (U remainderRef, -1)])
  --    0 ≤ remainder < divisor
  assertLTU width (Left remainderRef) (Left divisorRef)
  -- --    0 < divisor
  -- -- =>
  -- --    divisor != 0
  assertGT width divisor 0

--------------------------------------------------------------------------------

assertLTE2 :: (GaloisField n, Integral n) => Width -> Either RefU n -> Integer -> M n ()
assertLTE2 _ (Right a) c = if fromIntegral a <= c then return () else throwError $ Compile.AssertLTEBoundTooSmallError c
assertLTE2 width (Left a) c = assertLTE width a c

-- | Assert that a UInt is less than or equal to some constant
-- reference doc: A.3.2.2 Range Check https://zips.z.cash/protocol/protocol.pdf
assertLTE :: (GaloisField n, Integral n) => Width -> RefU -> Integer -> M n ()
assertLTE width a c = do
  -- check if the bound is within the range of the UInt
  when (c < 0) $
    throwError $
      Compile.AssertLTEBoundTooSmallError c
  when (c >= 2 ^ width - 1) $
    throwError $
      Compile.AssertLTEBoundTooLargeError c width

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
              if keepCounting && Data.Bits.testBit c i then (count + 1, True) else (count, False)
          )
          (0, True)
          [0 .. width - 1]

    go :: (GaloisField n, Integral n) => RefU -> Maybe Ref -> Int -> M n (Maybe Ref)
    go ref Nothing i =
      let aBit = RefUBit width ref i
       in -- have not found the first bit in 'c' that is 1 yet
          if Data.Bits.testBit c i
            then do
              return $ Just (B aBit) -- when found, return a[i]
            else do
              -- a[i] = 0
              writeValB aBit False
              return Nothing -- otherwise, continue searching
    go ref (Just acc) i =
      let aBit = B (RefUBit width ref i)
       in if Data.Bits.testBit c i
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
assertLT :: (GaloisField n, Integral n) => Width -> ExprU n -> Integer -> M n ()
assertLT width a c = do
  -- check if the bound is within the range of the UInt
  when (c < 1) $
    throwError $
      Compile.AssertLTBoundTooSmallError c
  when (c >= 2 ^ width) $
    throwError $
      Compile.AssertLTBoundTooLargeError c width
  -- otherwise, assert that a <= c - 1
  a' <- wireU' a
  assertLTE2 width a' (c - 1)

-- | Assert that a UInt is greater than or equal to some constant
assertGTE :: (GaloisField n, Integral n) => Width -> ExprU n -> Integer -> M n ()
assertGTE width a bound = do
  -- check if the bound is within the range of the UInt
  when (bound < 1) $
    throwError $
      Compile.AssertGTEBoundTooSmallError bound
  when (bound >= 2 ^ width) $
    throwError $
      Compile.AssertGTEBoundTooLargeError bound width

  ref <- wireU a
  flag <- freshRefF
  writeValF flag 1
  -- because we don't have to execute the `go` function for trailing zeros of `bound`
  -- we can limit the range of bits of c from `[width-1, width-2 .. 0]` to `[width-1, width-2 .. countTrailingZeros]`
  -- foldM_ (go ref) (F flag) [width - 1, width - 2 .. 0]
  foldM_ (go ref) (F flag) [width - 1, width - 2 .. (width - 2) `min` countTrailingZeros]
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
assertGT :: (GaloisField n, Integral n) => Width -> ExprU n -> Integer -> M n ()
assertGT width a c = do
  -- check if the bound is within the range of the UInt
  when (c < 0) $
    throwError $
      Compile.AssertGTBoundTooSmallError c
  when (c >= 2 ^ width - 1) $
    throwError $
      Compile.AssertGTBoundTooLargeError c width
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
    else throwError $ Compile.ConflictingValuesF val val'
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