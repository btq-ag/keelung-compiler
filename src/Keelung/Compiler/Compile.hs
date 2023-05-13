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

import Data.Either (partitionEithers)
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (foldl'), toList)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq (..))
import Keelung.Compiler.Compile.Error qualified as Compile
import Keelung.Compiler.Compile.Util
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintSystem
import Keelung.Compiler.Error
import Keelung.Compiler.Syntax.FieldBits qualified as FieldBits
import Keelung.Compiler.Syntax.Internal
import Keelung.Field (FieldType)
import Keelung.Syntax (widthOf)
import Keelung.Syntax.Counters (VarSort (..), VarType (..), addCount, getCount)

--------------------------------------------------------------------------------

-- | Compile an untyped expression to a constraint system
run :: (GaloisField n, Integral n) => (FieldType, Integer, Integer) -> Bool -> Internal n -> Either (Error n) (ConstraintSystem n)
run fieldInfo useNewOptimizer (Internal untypedExprs _ counters assertions sideEffects) = left CompileError $ runM fieldInfo useNewOptimizer counters $ do
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
        compileExprF out x
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
compileSideEffect (AssignmentF var val) = compileExprF (RefFX var) val
compileSideEffect (AssignmentU width var val) = compileExprU (RefUX width var) val
compileSideEffect (DivMod width dividend divisor quotient remainder) = assertDivModU width dividend divisor quotient remainder
compileSideEffect (AssertLTE width value bound) = assertLTE width value bound
compileSideEffect (AssertLT width value bound) = assertLT width value bound
compileSideEffect (AssertGTE width value bound) = assertGTE width value bound
compileSideEffect (AssertGT width value bound) = assertGT width value bound

-- | Compile the constraint 'out = x'.
compileAssertion :: (GaloisField n, Integral n) => Expr n -> M n ()
compileAssertion expr = case expr of
  ExprB (EqB x y) -> compileAssertionEqB x y
  ExprB (EqF x y) -> compileAssertionEqF x y
  ExprB (EqU x y) -> compileAssertionEqU x y
  -- rewriting `assert (x <= y)` width `assertLTE x y`
  ExprB (LTEU x (ValU width bound)) -> assertLTE width x (toInteger bound)
  ExprB (LTEU (ValU width bound) x) -> assertGTE width x (toInteger bound)
  ExprB (LTU x (ValU width bound)) -> assertLT width x (toInteger bound)
  ExprB (LTU (ValU width bound) x) -> assertGT width x (toInteger bound)
  ExprB (GTEU x (ValU width bound)) -> assertGTE width x (toInteger bound)
  ExprB (GTEU (ValU width bound) x) -> assertLTE width x (toInteger bound)
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
    out <- freshRefF
    compileExprF out x
    addC $ cVarBindF (F out) 1
  ExprU x -> do
    out <- freshRefU (widthOf x)
    compileExprU out x
    addC $ cVarBindU out 1

compileAssertionEqB :: (GaloisField n, Integral n) => ExprB n -> ExprB n -> M n ()
compileAssertionEqB (VarB a) (ValB b) = addC $ cVarBindB (RefBX a) b
compileAssertionEqB (VarB a) (VarB b) = addC $ cVarEqB (RefBX a) (RefBX b)
compileAssertionEqB (VarB a) (VarBO b) = addC $ cVarEqB (RefBX a) (RefBO b)
compileAssertionEqB (VarB a) (VarBI b) = addC $ cVarEqB (RefBX a) (RefBI b)
compileAssertionEqB (VarB a) b = do
  result <- compileExprB b
  case result of
    Left var -> writeEqB (RefBX a) var
    Right val -> writeValB (RefBX a) val
compileAssertionEqB (VarBO a) (ValB b) = addC $ cVarBindB (RefBO a) b
compileAssertionEqB (VarBO a) (VarB b) = addC $ cVarEqB (RefBO a) (RefBX b)
compileAssertionEqB (VarBO a) (VarBO b) = addC $ cVarEqB (RefBO a) (RefBO b)
compileAssertionEqB (VarBO a) (VarBI b) = addC $ cVarEqB (RefBO a) (RefBI b)
compileAssertionEqB (VarBO a) b = do
  result <- compileExprB b
  case result of
    Left var -> writeEqB (RefBO a) var
    Right val -> writeValB (RefBO a) val
compileAssertionEqB (VarBI a) (ValB b) = addC $ cVarBindB (RefBI a) b
compileAssertionEqB (VarBI a) (VarB b) = addC $ cVarEqB (RefBI a) (RefBX b)
compileAssertionEqB (VarBI a) (VarBO b) = addC $ cVarEqB (RefBI a) (RefBO b)
compileAssertionEqB (VarBI a) (VarBI b) = addC $ cVarEqB (RefBI a) (RefBI b)
compileAssertionEqB (VarBI a) b = do
  result <- compileExprB b
  case result of
    Left var -> writeEqB (RefBI a) var
    Right val -> writeValB (RefBI a) val
compileAssertionEqB a b = do
  a' <- compileExprB a
  b' <- compileExprB b
  case (a', b') of
    (Left varA, Left varB) -> writeEqB varA varB
    (Left varA, Right valB) -> writeValB varA valB
    (Right valA, Left varB) -> writeValB varB valA
    (Right valA, Right valB) -> when (valA /= valB) $ throwError $ Compile.ConflictingValuesB valA valB

compileAssertionEqF :: (GaloisField n, Integral n) => ExprF n -> ExprF n -> M n ()
compileAssertionEqF (VarF a) (ValF b) = addC $ cVarBindF (F $ RefFX a) b
compileAssertionEqF (VarF a) (VarF b) = addC $ cVarEqF (RefFX a) (RefFX b)
compileAssertionEqF (VarF a) (VarFO b) = addC $ cVarEqF (RefFX a) (RefFO b)
compileAssertionEqF (VarF a) (VarFI b) = addC $ cVarEqF (RefFX a) (RefFI b)
compileAssertionEqF (VarF a) b = do
  out <- freshRefF
  compileExprF out b
  addC $ cVarEqF (RefFX a) out
compileAssertionEqF (VarFO a) (ValF b) = addC $ cVarBindF (F $ RefFO a) b
compileAssertionEqF (VarFO a) (VarF b) = addC $ cVarEqF (RefFO a) (RefFX b)
compileAssertionEqF (VarFO a) (VarFO b) = addC $ cVarEqF (RefFO a) (RefFO b)
compileAssertionEqF (VarFO a) b = do
  out <- freshRefF
  compileExprF out b
  addC $ cVarEqF (RefFO a) out
compileAssertionEqF (VarFI a) (ValF b) = addC $ cVarBindF (F $ RefFI a) b
compileAssertionEqF (VarFI a) (VarF b) = addC $ cVarEqF (RefFI a) (RefFX b)
compileAssertionEqF (VarFI a) (VarFO b) = addC $ cVarEqF (RefFI a) (RefFX b)
compileAssertionEqF (VarFI a) b = do
  out <- freshRefF
  compileExprF out b
  addC $ cVarEqF (RefFI a) out
compileAssertionEqF a b = do
  a' <- freshRefF
  b' <- freshRefF
  compileExprF a' a
  compileExprF b' b
  addC $ cVarEqF a' b'

compileAssertionEqU :: (GaloisField n, Integral n) => ExprU n -> ExprU n -> M n ()
compileAssertionEqU (VarU w a) (ValU _ b) = addC $ cVarBindU (RefUX w a) b
compileAssertionEqU (VarU w a) (VarU _ b) = addC $ cVarEqU (RefUX w a) (RefUX w b)
compileAssertionEqU (VarU w a) (VarUO _ b) = addC $ cVarEqU (RefUX w a) (RefUO w b)
compileAssertionEqU (VarU w a) (VarUI _ b) = addC $ cVarEqU (RefUX w a) (RefUI w b)
compileAssertionEqU (VarU w a) b = do
  out <- freshRefU w
  compileExprU out b
  addC $ cVarEqU (RefUX w a) out
compileAssertionEqU (VarUO w a) (ValU _ b) = addC $ cVarBindU (RefUO w a) b
compileAssertionEqU (VarUO w a) (VarU _ b) = addC $ cVarEqU (RefUO w a) (RefUX w b)
compileAssertionEqU (VarUO w a) (VarUO _ b) = addC $ cVarEqU (RefUO w a) (RefUO w b)
compileAssertionEqU (VarUO w a) b = do
  out <- freshRefU w
  compileExprU out b
  addC $ cVarEqU (RefUO w a) out
compileAssertionEqU (VarUI w a) (ValU _ b) = addC $ cVarBindU (RefUI w a) b
compileAssertionEqU (VarUI w a) (VarU _ b) = addC $ cVarEqU (RefUI w a) (RefUX w b)
compileAssertionEqU (VarUI w a) (VarUO _ b) = addC $ cVarEqU (RefUI w a) (RefUO w b)
compileAssertionEqU (VarUI w a) b = do
  out <- freshRefU w
  compileExprU out b
  addC $ cVarEqU (RefUI w a) out
compileAssertionEqU a b = do
  let width = widthOf a
  a' <- freshRefU width
  b' <- freshRefU width
  compileExprU a' a
  compileExprU b' b
  addC $ cVarEqU a' b'

-- compileRelations :: (GaloisField n, Integral n) => Relations n -> M n ()
-- compileRelations (Relations vb eb) = do
--   -- intermediate variable bindings of values
--   forM_ (IntMap.toList (structF vb)) $ \(var, val) -> addC $ cVarBindF (RefF var) val
--   forM_ (IntMap.toList (structB vb)) $ \(var, val) -> addC $ cVarBindB (RefB var) val
--   forM_ (IntMap.toList (structU vb)) $ \(width, bindings) ->
--     forM_ (IntMap.toList bindings) $ \(var, val) -> addC $ cVarBindU (RefUX width var) val
--   -- intermediate variable bindings of expressions
--   forM_ (IntMap.toList (structF eb)) $ \(var, val) -> compileExprF (RefF var) val
--   forM_ (IntMap.toList (structB eb)) $ \(var, val) -> compileExprB (RefB var) val
--   forM_ (IntMap.toList (structU eb)) $ \(width, bindings) ->
--     forM_ (IntMap.toList bindings) $ \(var, val) -> compileExprU (RefUX width var) val

--------------------------------------------------------------------------------

addEqHint :: (GaloisField n, Integral n) => Ref -> Either Ref n -> RefF -> M n ()
addEqHint x y z = modify' $ \cs -> cs {csEqs = Map.insert (x, y) z (csEqs cs)}

addDivModHint :: (GaloisField n, Integral n) => RefU -> RefU -> RefU -> RefU -> M n ()
addDivModHint x y q r = modify' $ \cs -> cs {csDivMods = (Left x, Left y, Left q, Left r) : csDivMods cs}

addModInvHint :: (GaloisField n, Integral n) => RefU -> RefU -> Integer -> M n ()
addModInvHint x n p = modify' $ \cs -> cs {csModInvs = (Left x, Left n, p) : csModInvs cs}

freshExprU :: Width -> M n (ExprU n)
freshExprU width = do
  counters <- gets csCounters
  let index = getCount OfIntermediate (OfUInt width) counters
  modifyCounter $ addCount OfIntermediate (OfUInt width) 1
  return $ VarU width index

----------------------------------------------------------------

compileExprB :: (GaloisField n, Integral n) => ExprB n -> M n (Either RefB Bool)
compileExprB expr = case expr of
  ValB val -> return $ Right val -- out = val
  VarB var -> return $ Left (RefBX var) -- out = var
  VarBO var -> return $ Left (RefBO var) -- out = var
  VarBI var -> return $ Left (RefBI var) -- out = var
  VarBP var -> return $ Left (RefBP var) -- out = var
  AndB x0 x1 xs -> do
    x0' <- compileExprB x0
    x1' <- compileExprB x1
    xs' <- mapM compileExprB xs
    andBs x0' x1' xs'
  OrB x0 x1 xs -> do
    x0' <- compileExprB x0
    x1' <- compileExprB x1
    xs' <- mapM compileExprB xs
    orBs x0' x1' xs'
  XorB x y -> do
    x' <- compileExprB x
    y' <- compileExprB y
    xorB x' y'
  NotB x -> do
    x' <- compileExprB x
    case x' of
      Left var -> do
        out <- freshRefB
        writeNEqB var out
        return $ Left out
      Right val -> return $ Right (not val)
  IfB p x y -> do
    p' <- compileExprB p
    x' <- compileExprB x
    y' <- compileExprB y
    compileIfB p' x' y'
  NEqB x y -> compileExprB (XorB x y)
  NEqF x y -> do
    x' <- wireF' x
    y' <- wireF' y
    eqFU False (left F x') (left F y')
  NEqU x y -> do
    x' <- wireU' x
    y' <- wireU' y
    eqFU False (left U x') (left U y')
  EqB x y -> do
    x' <- compileExprB x
    y' <- compileExprB y
    eqB x' y'
  EqF x y -> do
    x' <- wireF' x
    y' <- wireF' y
    eqFU True (left F x') (left F y')
  EqU x y -> do
    x' <- wireU' x
    y' <- wireU' y
    eqFU True (left U x') (left U y')
  LTEU x y -> do
    x' <- wireU' x
    y' <- wireU' y
    case (x', y') of
      (Left xVar, Left yVar) -> computeLTEUVarVar xVar yVar
      (Left xVar, Right yVal) -> computeLTEUVarConst xVar yVal
      (Right xVal, Left yVar) -> computeLTEUConstVar xVal yVar
      (Right xVal, Right yVal) -> return $ Right (xVal <= yVal)
  LTU x y -> do
    x' <- wireU' x
    y' <- wireU' y
    case (x', y') of
      (Left xVar, Left yVar) -> computeLTUVarVar xVar yVar
      (Left xVar, Right yVal) -> computeLTUVarConst xVar yVal
      (Right xVal, Left yVar) -> computeLTUConstVar xVal yVar
      (Right xVal, Right yVal) -> return $ Right (xVal < yVal)
  GTEU x y -> compileExprB (LTEU y x)
  GTU x y -> compileExprB (LTU y x)
  BitU (ValU width val) i -> do
    let index = i `mod` width
    let bit = FieldBits.testBit' val index
    return $ Right bit
  BitU x i -> do
    x' <- wireU x
    let width = widthOf x
    return $ Left (RefUBit width x' (i `mod` width)) -- out = x'[i]

compileExprF :: (GaloisField n, Integral n) => RefF -> ExprF n -> M n ()
compileExprF out expr = case expr of
  ValF val -> addC $ cVarBindF (F out) val -- out = val
  VarF var -> addC $ cVarEqF out (RefFX var) -- out = var
  VarFO var -> addC $ cVarEqF out (RefFO var) -- out = var
  VarFI var -> addC $ cVarEqF out (RefFI var) -- out = var
  VarFP var -> addC $ cVarEqF out (RefFP var) -- out = var
  SubF x y -> do
    x' <- toTerm x
    y' <- toTerm y
    compileTerms out (x' :<| negateTerm y' :<| Empty)
  AddF x y rest -> do
    terms <- mapM toTerm (x :<| y :<| rest)
    compileTerms out terms
  MulF x y -> do
    x' <- wireF x
    y' <- wireF y
    addC $ cMulSimpleF (F x') (F y') (F out)
  ExpF x n -> do
    base <- wireF x
    result <- fastExp (F base) (Right 1) n
    case result of
      Left var -> addC $ cVarEq (F out) var
      Right val -> addC $ cVarBindF (F out) val
  DivF x y -> do
    x' <- wireF x
    y' <- wireF y
    addC $ cMulSimpleF (F y') (F out) (F x')
  -- MMIF x p -> do
  --   -- See: https://github.com/btq-ag/keelung-compiler/issues/14
  --   -- 1. x * x⁻¹ = np + 1
  --   -- 2. n ≤ ⌈log₂p⌉

  --   -- constraint: n ≤ ⌈log₂p⌉
  --   let upperBoundOfN = ceiling (logBase 2 (fromIntegral p) :: Double) :: Integer
  --   let bitWidthOfUIntThatCanStoreUpperBoundOfN = ceiling (logBase 2 (fromIntegral upperBoundOfN) :: Double) :: Int
  --   n <- freshRefU  bitWidthOfUIntThatCanStoreUpperBoundOfN
  --   let diff = 2 ^ bitWidthOfUIntThatCanStoreUpperBoundOfN - upperBoundOfN

  --   -- constraint: x * x⁻¹ = np + 1
  --   x' <- wireF x
  --   inv <- freshRefF
  --   addC $ cMulF (0, [(x', 1)]) (0, [(inv, -1)]) (1, [(U n, fromIntegral p)])
  IfF p x y -> do
    p' <- compileExprB p
    x' <- wireF' x
    y' <- wireF' y
    result <- compileIfF p' x' y'
    case result of
      Left var -> addC $ cVarEq (F out) (F var)
      Right val -> addC $ cVarBindF (F out) val
  BtoF x -> do
    result <- compileExprB x
    case result of
      Left var -> addC $ cVarEq (F out) (B var) -- out = var
      Right True -> addC $ cVarBindF (F out) 1
      Right False -> addC $ cVarBindF (F out) 0

compileExprU :: (GaloisField n, Integral n) => RefU -> ExprU n -> M n ()
compileExprU out expr = case expr of
  ValU _ val -> do
    addC $ cVarBindU out val
  VarU width var -> do
    addC $ cVarEqU out (RefUX width var)
  VarUO width var -> do
    addC $ cVarEqU out (RefUX width var) -- out = var
  VarUI width var -> do
    let ref = RefUI width var
    -- constraint for UInt : out = ref
    addC $ cVarEqU out ref
    -- constraints for BinRep of UInt
    forM_ [0 .. width - 1] $ \i -> do
      addC $ cVarEqB (RefUBit width out i) (RefUBit width ref i) -- out[i] = ref[i]
  VarUP width var -> do
    let ref = RefUP width var
    -- constraint for UInt : out = ref
    addC $ cVarEqU out ref
    -- constraints for BinRep of UInt
    forM_ [0 .. width - 1] $ \i -> do
      addC $ cVarEqB (RefUBit width out i) (RefUBit width ref i) -- out[i] = ref[i]
  SubU w x y -> do
    x' <- wireU x
    y' <- wireU y
    compileSubU w out x' y'
  AddU w x y -> do
    x' <- wireU x
    y' <- wireU y
    compileAddU w out x' y'
  MulU w x y -> do
    x' <- wireU x
    y' <- wireU y
    compileMulU w out x' y'
  MMIU w a p -> do
    -- See: https://github.com/btq-ag/keelung-compiler/issues/14
    -- 1. a * a⁻¹ = np + 1
    -- 2. n ≤ ⌈log₂p⌉
    a' <- wireU a
    n <- freshExprU w
    nRef <- wireU n
    let ceilingLg2P = ceiling (logBase 2 (fromInteger p) :: Double)
    addC $ cMulF (0, [(U a', 1)]) (0, [(U out, 1)]) (1, [(U nRef, fromInteger p)])
    addModInvHint a' nRef p
    assertLTE w n ceilingLg2P
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
    x' <- wireU x
    -- addC $ cRotateU out x' n
    forM_ [0 .. w - 1] $ \i -> do
      let i' = (i - n) `mod` w
      addC $ cVarEqB (RefUBit w out i) (RefUBit w x' i') -- out[i] = x'[i']
  ShLU w n x -> do
    x' <- wireU x
    case compare n 0 of
      EQ -> addC $ cVarEqU out x'
      GT -> do
        -- fill lower bits with 0s
        forM_ [0 .. n - 1] $ \i -> do
          addC $ cVarBindB (RefUBit w out i) False -- out[i] = 0
          -- shift upper bits
        forM_ [n .. w - 1] $ \i -> do
          let i' = i - n
          addC $ cVarEqB (RefUBit w out i) (RefUBit w x' i') -- out[i] = x'[i']
      LT -> do
        -- shift lower bits
        forM_ [0 .. w + n - 1] $ \i -> do
          let i' = i - n
          addC $ cVarEqB (RefUBit w out i) (RefUBit w x' i') -- out[i] = x'[i']
          -- fill upper bits with 0s
        forM_ [w + n .. w - 1] $ \i -> do
          addC $ cVarBindB (RefUBit w out i) False -- out[i] = 0
  SetU w x j b -> do
    x' <- wireU x
    b' <- wireB b
    forM_ [0 .. w - 1] $ \i -> do
      if i == j
        then addC $ cVarEqB (RefUBit w out i) b' -- out[i] = b
        else addC $ cVarEqB (RefUBit w out i) (RefUBit w x' i) -- out[i] = x[i]
  BtoU w x -> do
    -- 1. wire 'out[ZERO]' to 'x'
    result <- compileExprB x

    case result of
      Left var -> writeEqB (RefUBit w out 0) var -- out[0] = x
      Right val -> writeValB (RefUBit w out 0) val -- out[0] = x
      -- 2. wire 'out[SUCC _]' to '0' for all other bits
    forM_ [1 .. w - 1] $ \i ->
      addC $ cVarBindB (RefUBit w out i) False -- out[i] = 0

--------------------------------------------------------------------------------

data Term n
  = Constant n -- c
  | WithVars RefF n -- cx

-- Avoid having to introduce new multiplication gates
-- for multiplication by constant scalars.
toTerm :: (GaloisField n, Integral n) => ExprF n -> M n (Term n)
toTerm (MulF (ValF m) (ValF n)) = return $ Constant (m * n)
toTerm (MulF (VarF var) (ValF n)) = return $ WithVars (RefFX var) n
toTerm (MulF (VarFI var) (ValF n)) = return $ WithVars (RefFI var) n
toTerm (MulF (VarFO var) (ValF n)) = return $ WithVars (RefFO var) n
toTerm (MulF (ValF n) (VarF var)) = return $ WithVars (RefFX var) n
toTerm (MulF (ValF n) (VarFI var)) = return $ WithVars (RefFI var) n
toTerm (MulF (ValF n) (VarFO var)) = return $ WithVars (RefFO var) n
toTerm (MulF (ValF n) expr) = do
  out <- freshRefF
  compileExprF out expr
  return $ WithVars out n
toTerm (MulF expr (ValF n)) = do
  out <- freshRefF
  compileExprF out expr
  return $ WithVars out n
toTerm (ValF n) =
  return $ Constant n
toTerm (VarF var) =
  return $ WithVars (RefFX var) 1
toTerm (VarFI var) =
  return $ WithVars (RefFI var) 1
toTerm (VarFO var) =
  return $ WithVars (RefFO var) 1
toTerm expr = do
  out <- freshRefF
  compileExprF out expr
  return $ WithVars out 1

-- | Negate a Term
negateTerm :: Num n => Term n -> Term n
negateTerm (WithVars var c) = WithVars var (negate c)
negateTerm (Constant c) = Constant (negate c)

compileTerms :: (GaloisField n, Integral n) => RefF -> Seq (Term n) -> M n ()
compileTerms out terms =
  let (constant, varsWithCoeffs) = foldl' go (0, []) terms
   in case varsWithCoeffs of
        [] -> addC $ cVarBindF (F out) constant
        _ -> addC $ cAddF constant $ (F out, -1) : varsWithCoeffs
  where
    go :: Num n => (n, [(Ref, n)]) -> Term n -> (n, [(Ref, n)])
    go (constant, pairs) (Constant n) = (constant + n, pairs)
    go (constant, pairs) (WithVars var coeff) = (constant, (F var, coeff) : pairs)

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

wireF :: (GaloisField n, Integral n) => ExprF n -> M n RefF
wireF (VarF ref) = return (RefFX ref)
wireF (VarFO ref) = return (RefFO ref)
wireF (VarFI ref) = return (RefFI ref)
wireF (VarFP ref) = return (RefFP ref)
wireF expr = do
  out <- freshRefF
  compileExprF out expr
  return out

wireF' :: (GaloisField n, Integral n) => ExprF n -> M n (Either RefF n)
wireF' (ValF val) = return (Right val)
wireF' others = Left <$> wireF others

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

-- | Equalities are compiled with inequalities and inequalities with CNEQ constraints.
--    introduce a new variable m
--    if diff = 0 then m = 0 else m = recip diff
--    Equality:
--      (x - y) * m = 1 - out
--      (x - y) * out = 0
--    Inequality:
--      (x - y) * m = out
--      (x - y) * (1 - out) = 0
eqFU :: (GaloisField n, Integral n) => Bool -> Either Ref n -> Either Ref n -> M n (Either RefB Bool)
eqFU isEq (Right x) (Right y) = return $ Right $ if isEq then x == y else x /= y
eqFU isEq (Right x) (Left y) = do
  m <- freshRefF
  out <- freshRefB
  if isEq
    then do
      --  1. (x - y) * m = 1 - out
      --  2. (x - y) * out = 0
      writeMul
        (x, [(y, -1)])
        (0, [(F m, 1)])
        (1, [(B out, -1)])
      writeMul
        (x, [(y, -1)])
        (0, [(B out, 1)])
        (0, [])
    else do
      --  1. (x - y) * m = out
      --  2. (x - y) * (1 - out) = 0
      writeMul
        (x, [(y, -1)])
        (0, [(F m, 1)])
        (0, [(B out, 1)])
      writeMul
        (x, [(y, -1)])
        (1, [(B out, -1)])
        (0, [])
  --  keep track of the relation between (x - y) and m
  addEqHint y (Right x) m
  return (Left out)
eqFU isEq (Left x) (Right y) = eqFU isEq (Right y) (Left x)
eqFU isEq (Left x) (Left y) = do
  m <- freshRefF
  out <- freshRefB
  if isEq
    then do
      --  1. (x - y) * m = 1 - out
      --  2. (x - y) * out = 0
      writeMul
        (0, [(x, 1), (y, -1)])
        (0, [(F m, 1)])
        (1, [(B out, -1)])
      writeMul
        (0, [(x, 1), (y, -1)])
        (0, [(B out, 1)])
        (0, [])
    else do
      --  1. (x - y) * m = out
      --  2. (x - y) * (1 - out) = 0
      writeMul
        (0, [(x, 1), (y, -1)])
        (0, [(F m, 1)])
        (0, [(B out, 1)])
      writeMul
        (0, [(x, 1), (y, -1)])
        (1, [(B out, -1)])
        (0, [])
  --  keep track of the relation between (x - y) and m
  addEqHint y (Left x) m
  return (Left out)

eqB :: (GaloisField n, Integral n) => Either RefB Bool -> Either RefB Bool -> M n (Either RefB Bool)
eqB (Right x) (Right y) = return $ Right $ x == y
eqB (Right True) (Left y) = return $ Left y
eqB (Right False) (Left y) = do
  out <- freshRefB
  writeNEqB out y
  return $ Left out
eqB (Left x) (Right y) = eqB (Right y) (Left x)
eqB (Left x) (Left y) = do
  --     x * y + (1 - x) * (1 - y) = out
  -- =>
  --    (1 - x) * (1 - 2y) = (out - y)
  out <- freshRefB
  writeMul
    (1, [(B x, -1)])
    (1, [(B y, -2)])
    (0, [(B out, 1), (B y, -1)])
  return (Left out)

--------------------------------------------------------------------------------

-- | Encoding addition on UInts with multiple operands: O(1)
--      A       =          2ⁿAₙ₋₁ + ... + 2A₁ + A₀
--      B       =          2ⁿBₙ₋₁ + ... + 2B₁ + B₀
--      C       = 2ⁿ⁺¹Cₙ + 2ⁿCₙ₋₁ + ... + 2C₁ + C₀
--      Result  =          2ⁿCₙ₋₁ + ... + 2C₁ + C₀
--      C       = A + B
compileAddOrSubU :: (GaloisField n, Integral n) => Bool -> Width -> RefU -> RefU -> RefU -> M n ()
compileAddOrSubU isSub width out a b = do
  c <- freshRefU (width + 1)
  -- C = A + B
  addC $ cAddF 0 [(U a, 1), (U b, if isSub then -1 else 1), (U c, -1)]
  -- copying bits from C to 'out'
  forM_ [0 .. width - 1] $ \i -> do
    -- Cᵢ = outᵢ
    addC $ cVarEqB (RefUBit width c i) (RefUBit width out i)

-- HACK: addC occurences of RefUs
-- addOccurrencesUTemp [out, a, b, c]

compileAddU :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
compileAddU = compileAddOrSubU False

compileSubU :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
compileSubU = compileAddOrSubU True

-- | Encoding addition on UInts with multiple operands: O(2)
--      A       =   2ⁿAₙ₋₁ + ... + 2A₁ + A₀
--      B       =   2ⁿBₙ₋₁ + ... + 2B₁ + B₀
--      C       = 2²ⁿC₂ₙ₋₁ + ... + 2C₁ + C₀
--      Result  =   2ⁿCₙ₋₁ + ... + 2C₁ + C₀
--      C       = A * B
compileMulU :: (GaloisField n, Integral n) => Int -> RefU -> RefU -> RefU -> M n ()
compileMulU width out a b = do
  c <- freshRefU (width * 2)
  -- C = A * B
  addC $ cMulF (0, [(U a, 1)]) (0, [(U b, 1)]) (0, [(U c, 1)])
  -- copying bits from C to 'out'
  forM_ [0 .. width - 1] $ \i -> do
    -- Cᵢ = outᵢ
    addC $ cVarEqB (RefUBit width c i) (RefUBit width out i)

-- HACK: addC occurences of RefUs
-- addOccurrencesUTemp [out, a, b, c]

-- | Conditional
--  out = p * x + (1 - p) * y
--      =>
--  out = p * x + y - p * y
--      =>
--  (out - y) = p * (x - y)
compileIfF :: (GaloisField n, Integral n) => Either RefB Bool -> Either RefF n -> Either RefF n -> M n (Either RefF n)
compileIfF (Right True) x _ = return x
compileIfF (Right False) _ y = return y
compileIfF (Left p) (Right x) (Right y) = do
  if x == y
    then return $ Right x
    else do
      out <- freshRefF
      -- (x - y) * p - out + y = 0
      writeAdd y [(B p, x - y), (F out, -1)]
      return $ Left out
compileIfF (Left p) (Right x) (Left y) = do
  out <- freshRefF
  -- (out - y) = p * (x - y)
  writeMul
    (0, [(B p, 1)])
    (x, [(F y, -1)])
    (0, [(F y, -1), (F out, 1)])
  return $ Left out
compileIfF (Left p) (Left x) (Right y) = do
  out <- freshRefF
  -- (out - y) = p * (x - y)
  writeMul
    (0, [(B p, 1)])
    (-y, [(F x, 1)])
    (-y, [(F out, 1)])
  return $ Left out
compileIfF (Left p) (Left x) (Left y) = do
  out <- freshRefF
  -- (out - y) = p * (x - y)
  writeMul
    (0, [(B p, 1)])
    (0, [(F x, 1), (F y, -1)])
    (0, [(F y, -1), (F out, 1)])
  return $ Left out

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

-- | Conditional
--  out = p * x + (1 - p) * y
--      =>
--  out = p * x + y - p * y
--      =>
--  (out - y) = p * (x - y)
compileIfB :: (GaloisField n, Integral n) => Either RefB Bool -> Either RefB Bool -> Either RefB Bool -> M n (Either RefB Bool)
compileIfB (Right True) x _ = return x
compileIfB (Right False) _ y = return y
compileIfB (Left _) (Right True) (Right True) = return $ Right True
compileIfB (Left p) (Right True) (Right False) = return $ Left p
compileIfB (Left p) (Right False) (Right True) = do
  out <- freshRefB
  writeNEqB p out
  return $ Left out
compileIfB (Left _) (Right False) (Right False) = return $ Right False
compileIfB (Left p) (Right x) (Left y) = do
  out <- freshRefB
  -- (out - y) = p * (x - y)
  writeMul
    (0, [(B p, 1)])
    (if x then 1 else 0, [(B y, -1)])
    (0, [(B y, -1), (B out, 1)])
  return $ Left out
compileIfB (Left p) (Left x) (Right y) = do
  out <- freshRefB
  -- (out - y) = p * (x - y)
  writeMul
    (0, [(B p, 1)])
    (if y then -1 else 0, [(B x, 1)])
    (if y then -1 else 0, [(B out, 1)])
  return $ Left out
compileIfB (Left p) (Left x) (Left y) = do
  out <- freshRefB
  -- (out - y) = p * (x - y)
  writeMul
    (0, [(B p, 1)])
    (0, [(B x, 1), (B y, -1)])
    (0, [(B y, -1), (B out, 1)])
  return $ Left out

fromB :: Num n => Either RefB Bool -> Either Ref n
fromB (Right True) = Right 1
fromB (Right False) = Right 0
fromB (Left x) = Left $ B x

andBs :: (GaloisField n, Integral n) => Either RefB Bool -> Either RefB Bool -> Seq (Either RefB Bool) -> M n (Either RefB Bool)
andBs (Right False) _ _ = return $ Right False
andBs _ (Right False) _ = return $ Right False
andBs (Right True) x Empty = return x
andBs (Right True) x0 (x1 :<| xs) = andBs x0 x1 xs
andBs (Left x) (Right True) Empty = return $ Left x
andBs (Left x0) (Right True) (x1 :<| xs) = andBs (Left x0) x1 xs
andBs (Left x0) (Left x1) Empty = do
  -- 2 operands only
  -- x * y = out
  out <- freshRefB
  writeMul
    (0, [(B x0, 1)])
    (0, [(B x1, 1)])
    (0, [(B out, 1)])
  return $ Left out
andBs (Left x0) (Left x1) (x2 :<| xs) = do
  -- more than 2 operands, rewrite it as an equality instead:
  --      if all operands are 1           then 1 else 0
  --  =>  if the sum of operands is N     then 1 else 0
  --  =>  the sum of operands is N
  sumOfOperands <- add ((Left . B) x0) ((Left . B) x1) (fmap fromB (x2 :<| xs))
  eqFU True (Right (fromIntegral (3 + length xs))) sumOfOperands

orBs :: (GaloisField n, Integral n) => Either RefB Bool -> Either RefB Bool -> Seq (Either RefB Bool) -> M n (Either RefB Bool)
orBs (Right True) _ _ = return $ Right True
orBs _ (Right True) _ = return $ Right True
orBs (Right False) x Empty = return x
orBs (Right False) x0 (x1 :<| xs) = orBs x0 x1 xs
orBs (Left x) (Right False) Empty = return $ Left x
orBs (Left x0) (Right False) (x1 :<| xs) = orBs (Left x0) x1 xs
orBs (Left x0) (Left x1) Empty = do
  -- 2 operands only
  -- (1 - x) * y = (out - x)
  out <- freshRefB
  writeMul
    (1, [(B x0, -1)])
    (0, [(B x1, 1)])
    (0, [(B x0, -1), (B out, 1)])
  return $ Left out
orBs (Left x0) (Left x1) (x2 :<| xs) = do
  -- more than 2 operands, rewrite it as an inequality instead:
  --      if all operands are 0           then 0 else 1
  --  =>  if the sum of operands is 0     then 0 else 1
  --  =>  if the sum of operands is not 0 then 1 else 0
  --  =>  the sum of operands is not 0
  sumOfOperands <- add ((Left . B) x0) ((Left . B) x1) (fmap fromB (x2 :<| xs))
  eqFU False (Right 0) sumOfOperands

xorB :: (GaloisField n, Integral n) => Either RefB Bool -> Either RefB Bool -> M n (Either RefB Bool)
xorB (Right True) (Right True) = return $ Right False
xorB (Right True) (Right False) = return $ Right True
xorB (Right False) (Right True) = return $ Right True
xorB (Right False) (Right False) = return $ Right False
xorB (Right True) (Left y) = do
  out <- freshRefB
  writeNEqB out y
  return $ Left out
xorB (Right False) (Left y) = return $ Left y
xorB (Left x) (Right y) = xorB (Right y) (Left x)
xorB (Left x) (Left y) = do
  -- (1 - 2x) * (y + 1) = (1 + out - 3x)
  out <- freshRefB
  writeMul
    (1, [(B x, -2)])
    (1, [(B y, 1)])
    (1, [(B x, -3), (B out, 1)])
  return $ Left out

--------------------------------------------------------------------------------

assertNotZeroU :: (GaloisField n, Integral n) => Width -> ExprU n -> M n ()
assertNotZeroU width expr = do
  ref <- wireU expr
  -- introduce a new variable m, such that `expr * m = 1`
  m <- freshRefU width
  addC $
    cMulF
      (0, [(U ref, 1)])
      (0, [(U m, 1)])
      (1, [])

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
assertLTU :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> M n ()
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
  addDivModHint dividendRef divisorRef quotientRef remainderRef
  addC $
    cMulF
      (0, [(U divisorRef, 1)])
      (0, [(U quotientRef, 1)])
      (0, [(U dividendRef, 1), (U remainderRef, -1)])
  --    0 ≤ remainder < divisor
  assertLTU width remainderRef divisorRef
  -- --    0 < divisor
  -- -- =>
  -- --    divisor != 0
  assertNotZeroU width divisor

--------------------------------------------------------------------------------

-- | Assert that a UInt is less than or equal to some constant
-- reference doc: A.3.2.2 Range Check https://zips.z.cash/protocol/protocol.pdf
assertLTE :: (GaloisField n, Integral n) => Width -> ExprU n -> Integer -> M n ()
assertLTE width a c = do
  -- check if the bound is within the range of the UInt
  when (c < 0) $
    throwError $
      Compile.AssertLTEBoundTooSmallError c
  when (c >= 2 ^ width - 1) $
    throwError $
      Compile.AssertLTEBoundTooLargeError c width

  ref <- wireU a
  -- because we don't have to execute the `go` function for trailing ones of `c`
  -- we can limit the range of bits of c from `[width-1, width-2 .. 0]` to `[width-1, width-2 .. countTrailingOnes]`
  foldM_ (go ref) Nothing [width - 1, width - 2 .. (width - 2) `min` countTrailingOnes]
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
              addC $ cVarBindB aBit False
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
              addC $ cMulF (0, [(acc, 1)]) (0, [(aBit, 1)]) (0, [(F acc', 1)])
              return $ Just (F acc')
            else do
              -- constraint on a[i]
              -- (1 - acc - a[i]) * a[i] = 0
              -- such that if acc = 0 then a[i] = 0 or 1 (don't care)
              --           if acc = 1 then a[i] = 0
              addC $ cMulF (1, [(acc, -1), (aBit, -1)]) (0, [(aBit, 1)]) (0, [])
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
  assertLTE width a (c - 1)

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
  addC $ cVarBindF (F flag) 1
  foldM_ (go ref) (F flag) [width - 1, width - 2 .. 0]
  where
    go :: (GaloisField n, Integral n) => RefU -> Ref -> Int -> M n Ref
    go ref flag i =
      let aBit = RefUBit width ref i
          bBit = Data.Bits.testBit bound i
       in if bBit
            then do
              addC $ cMulF (1, [(B aBit, -1), (flag, -1)]) (0, [(B aBit, 1)]) (0, [(flag, -1)])
              return flag
            else do
              flag' <- freshRefF
              -- flag' := flag * (1 - bit)
              addC $ cMulF (0, [(flag, 1)]) (1, [(B aBit, -1)]) (0, [(F flag', 1)])
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

-- Compiling a ≤ b, where a and b are both variables
-- lastBit = if a
--    then if b then 1 else 0
--    else if b then 1 else 1
computeLTEUVarVar :: (GaloisField n, Integral n) => RefU -> RefU -> M n (Either RefB Bool)
computeLTEUVarVar x y = do
  let width = widthOf x
  -- last bit
  let xBit = B (RefUBit width x 0)
      yBit = B (RefUBit width y 0)
  -- x[0] * y[0] = result + x[0] - 1
  result <- freshRefB
  addC $ cMulF (0, [(xBit, 1)]) (0, [(yBit, 1)]) (-1, [(B result, 1), (xBit, 1)])
  -- starting from the least significant bit
  Left <$> foldM (compileLTEUVarVarPrim width x y) result [1 .. width - 1]

computeLTEUVarConst :: (GaloisField n, Integral n) => RefU -> n -> M n (Either RefB Bool)
computeLTEUVarConst x y = do
  let width = widthOf x
  -- starting from the least significant bit
  let pairs = [(RefUBit width x i, FieldBits.testBit' y i) | i <- [0 .. width - 1]]
  foldM compileLTEUVarConstPrim (Right True) pairs

computeLTEUConstVar :: (GaloisField n, Integral n) => n -> RefU -> M n (Either RefB Bool)
computeLTEUConstVar x y = do
  let width = widthOf y
  -- starting from the least significant bit
  let pairs = [(FieldBits.testBit' x i, RefUBit width y i) | i <- [0 .. width - 1]]
  foldM compileLTEUConstVarPrim (Right True) pairs

-- Compiling a < b, where a and b are both variables
-- lastBit = if a
--    then if b then 0 else 0
--    else if b then 1 else 0
-- (b - lastBit) = (a)(b)
computeLTUVarVar :: (GaloisField n, Integral n) => RefU -> RefU -> M n (Either RefB Bool)
computeLTUVarVar x y = do
  let width = widthOf x
  -- last bit
  let xBit = B (RefUBit width x 0)
      yBit = B (RefUBit width y 0)
  -- (y - lastBit) = (x)(y)
  lastBit <- freshRefB
  addC $ cMulF (0, [(xBit, 1)]) (0, [(yBit, 1)]) (0, [(B lastBit, -1), (yBit, 1)])
  -- starting from the least significant bit
  Left <$> foldM (compileLTEUVarVarPrim width x y) lastBit [1 .. width - 1]

-- output = if a
--    then if b then x else 0
--    else if b then 1 else x
-- output = 2abx + b + x - bx - ab - ax
--  =>
--  1. z = bx
--  2. output - z = (1-a)(b + x - 2z)
compileLTEUVarVarPrim :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefB -> Int -> M n RefB
compileLTEUVarVarPrim width x y acc i = do
  let xBit = B (RefUBit width x i)
      yBit = B (RefUBit width y i)

  -- yacc = y[i] * acc
  yacc <- freshRefB
  addC $ cMulF (0, [(yBit, 1)]) (0, [(B acc, 1)]) (0, [(B yacc, 1)])

  -- result - yacc = (1 - x[i]) * (y[i] + acc - 2 * yacc)
  result <- freshRefB
  addC $ cMulF (1, [(xBit, -1)]) (0, [(yBit, 1), (B acc, 1), (B yacc, -2)]) (0, [(B result, 1), (B yacc, -1)])

  return result

computeLTUVarConst :: (GaloisField n, Integral n) => RefU -> n -> M n (Either RefB Bool)
computeLTUVarConst x y = do
  let width = widthOf x
  -- starting from the least significant bit
  let pairs = [(RefUBit width x i, FieldBits.testBit' y i) | i <- [0 .. width - 1]]
  foldM compileLTEUVarConstPrim (Right False) pairs

computeLTUConstVar :: (GaloisField n, Integral n) => n -> RefU -> M n (Either RefB Bool)
computeLTUConstVar x y = do
  let width = widthOf y
  -- starting from the least significant bit
  let pairs = [(FieldBits.testBit' x i, RefUBit width y i) | i <- [0 .. width - 1]]
  foldM compileLTEUConstVarPrim (Right False) pairs

compileLTEUVarConstPrim :: (GaloisField n, Integral n) => Either RefB Bool -> (RefB, Bool) -> M n (Either RefB Bool)
compileLTEUVarConstPrim (Left acc) (x, True) = do
  -- result - acc = (1 - x[i]) * (1 - acc)
  result <- freshRefB
  addC $ cMulF (1, [(B x, -1)]) (1, [(B acc, -1)]) (0, [(B result, 1), (B acc, -1)])
  return $ Left result
compileLTEUVarConstPrim (Left acc) (x, False) = do
  -- result = (1 - x[i]) * acc
  result <- freshRefB
  addC $ cMulF (1, [(B x, -1)]) (0, [(B acc, 1)]) (0, [(B result, 1)])
  return $ Left result
compileLTEUVarConstPrim (Right True) (_, True) = return $ Right True
compileLTEUVarConstPrim (Right True) (x, False) = do
  result <- freshRefB
  addC $ cVarNEqB result x
  return $ Left result
compileLTEUVarConstPrim (Right False) (x, True) = do
  result <- freshRefB
  addC $ cVarNEqB result x
  return $ Left result
compileLTEUVarConstPrim (Right False) (_, False) = return $ Right False

compileLTEUConstVarPrim :: (GaloisField n, Integral n) => Either RefB Bool -> (Bool, RefB) -> M n (Either RefB Bool)
compileLTEUConstVarPrim (Left acc) (True, y) = do
  -- y[i] * acc = result
  result <- freshRefB
  addC $ cMulF (0, [(B y, 1)]) (0, [(B acc, 1)]) (0, [(B result, 1)])
  return $ Left result
compileLTEUConstVarPrim (Left acc) (_, y) = do
  -- - y[i] * acc = result - y[i] - acc
  result <- freshRefB
  addC $ cMulF (0, [(B y, -1)]) (0, [(B acc, 1)]) (0, [(B result, 1), (B y, -1), (B acc, -1)])
  return $ Left result
compileLTEUConstVarPrim (Right True) (True, y) = return $ Left y
compileLTEUConstVarPrim (Right True) (False, _) = return $ Right True
compileLTEUConstVarPrim (Right False) (True, _) = return $ Right False
compileLTEUConstVarPrim (Right False) (False, y) = return $ Left y

-- -- | Compute the addition of two variables
-- add :: (GaloisField n, Integral n) => Either Ref n -> Either Ref n -> M n (Either Ref n)
-- add (Left x) (Left y) = do
--   out <- freshRefF
--   addC $ cAddF 0 [(x, 1), (y, 1), (F out, -1)]
--   return $ Left (F out)
-- add (Left x) (Right y) = do
--   out <- freshRefF
--   addC $ cAddF y [(x, 1), (F out, -1)]
--   return $ Left (F out)
-- add (Right x) (Left y) = add (Left y) (Right x)
-- add (Right x) (Right y) = return $ Right (x + y)

-- | Compute the addition of two variables
add :: (GaloisField n, Integral n) => Either Ref n -> Either Ref n -> Seq (Either Ref n) -> M n (Either Ref n)
add x0 x1 xs = do
  out <- freshRefF
  let (variables, constants) = partitionEithers (x0 : x1 : toList xs)
  addC $ cAddF (sum constants) $ (F out, -1) : [(x, 1) | x <- variables]
  return $ Left (F out)

-- add (Left x) (Left y) Empty = do
--   out <- freshRefF
--   addC $ cAddF 0 [(x, 1), (y, 1), (F out, -1)]
--   return $ Left (F out)
-- add (Left x) (Left y) (z :<| xs) = _
-- add (Left x) (Right y) Empty = do
--   out <- freshRefF
--   addC $ cAddF y [(x, 1), (F out, -1)]
--   return $ Left (F out)
-- add (Left x) (Right y) (z :<| xs) = _
-- add (Right x) (Left y) Empty = add (Left y) (Right x) Empty
-- add (Right x) (Left y) (z :<| xs) = _
-- add (Right x) (Right y) Empty = return $ Right (x + y)
-- add (Right x) (Right y) (z :<| xs) = _

-- | Compute the multiplication of two variables
mul :: (GaloisField n, Integral n) => Either Ref n -> Either Ref n -> M n (Either Ref n)
mul (Left x) (Left y) = do
  out <- freshRefF
  writeMul (0, [(x, 1)]) (0, [(y, 1)]) (0, [(F out, 1)])
  return $ Left (F out)
mul (Left x) (Right y) = do
  out <- freshRefF
  writeAdd 0 [(x, fromIntegral y), (F out, -1)]
  return $ Left (F out)
mul (Right x) (Left y) = mul (Left y) (Right x)
mul (Right x) (Right y) = return $ Right (x * y)

-- | Fast exponentiation on field
fastExp :: (GaloisField n, Integral n) => Ref -> Either Ref n -> Integer -> M n (Either Ref n)
fastExp _ acc 0 = return acc
fastExp base acc e =
  let (q, r) = e `divMod` 2
   in if r == 1
        then do
          result <- fastExp base acc (e - 1)
          mul result (Left base)
        else do
          result <- fastExp base acc q
          mul result result

--------------------------------------------------------------------------------

-- compileExpr ::
--   (GaloisField n, Integral n) =>
--   Expr n ->
--   M n (Either Ref n)
-- compileExpr (ExprF expr) = do
--   out <- freshRefF
--   compileExprF out expr
--   return $ Left (F out)
-- compileExpr (ExprB expr) = do
--   out <- freshRefB
--   compileExprB out expr
--   return $ Left (B out)
-- compileExpr (ExprU expr) = do
--   out <- freshRefU (widthOf expr)
--   compileExprU out expr
--   return $ Left (U out)
