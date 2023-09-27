{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile (run) where

import Control.Arrow (left)
import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import Data.Map.Strict qualified as Map
import Keelung.Compiler.Compile.Boolean qualified as Boolean
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.Field qualified as Field
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Compile.UInt qualified as UInt
import Keelung.Compiler.ConstraintModule
import Keelung.Compiler.Error
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.FieldInfo (FieldInfo)
import Keelung.Data.LC
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Syntax (widthOf)

--------------------------------------------------------------------------------

-- | Compile an untyped expression to a constraint system
run :: (GaloisField n, Integral n) => FieldInfo -> Internal n -> Either (Error n) (ConstraintModule n)
run fieldInfo (Internal untypedExprs _ counters assertions sideEffects) = left CompilerError $ runM bootstrapCompilers fieldInfo counters $ do
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
        relateLC out result
      ExprU x -> do
        let out = RefUO (widthOf x) var
        compileExprU out x

  -- compile assertions to constraints
  mapM_ compileAssertion assertions

  -- compile all side effects
  mapM_ compileSideEffect sideEffects
  where
    bootstrapCompilers = BootstrapCompiler Field.compile (Boolean.compile UInt.wireU) UInt.compile

-- | Compile side effects
compileSideEffect :: (GaloisField n, Integral n) => SideEffect n -> M n ()
compileSideEffect (AssignmentB var val) = do
  result <- compileExprB val
  case result of
    Left var' -> writeEqB (RefBX var) var'
    Right val' -> writeValB (RefBX var) val'
compileSideEffect (AssignmentF var val) = do
  result <- compileExprF val
  relateLC (RefFX var) result
compileSideEffect (AssignmentU width var val) = compileExprU (RefUX width var) val
compileSideEffect (DivMod width dividend divisor quotient remainder) = UInt.assertDivModU compileAssertion width dividend divisor quotient remainder
compileSideEffect (AssertLTE width value bound) = do
  x <- UInt.wireU value
  UInt.assertLTE width x bound
compileSideEffect (AssertLT width value bound) = do
  x <- UInt.wireU value
  UInt.assertLT width x bound
compileSideEffect (AssertGTE width value bound) = do
  x <- UInt.wireU value
  UInt.assertGTE width x bound
compileSideEffect (AssertGT width value bound) = do
  x <- UInt.wireU value
  UInt.assertGT width x bound

-- | Compile the constraint 'out = x'.
compileAssertion :: (GaloisField n, Integral n) => Expr n -> M n ()
compileAssertion expr = case expr of
  ExprB (EqB x y) -> assertEqB x y
  ExprB (EqF x y) -> assertEqF x y
  ExprB (EqU x y) -> assertEqU x y
  -- rewriting `assert (x <= y)` width `UInt.assertLTE x y`
  ExprB (LTEU x (ValU width bound)) -> do
    x' <- UInt.wireU x
    UInt.assertLTE width x' (toInteger bound)
  ExprB (LTEU (ValU width bound) x) -> do
    x' <- UInt.wireU x
    UInt.assertGTE width x' (toInteger bound)
  ExprB (LTU x (ValU width bound)) -> do
    x' <- UInt.wireU x
    UInt.assertLT width x' (toInteger bound)
  ExprB (LTU (ValU width bound) x) -> do
    x' <- UInt.wireU x
    UInt.assertGT width x' (toInteger bound)
  ExprB (GTEU x (ValU width bound)) -> do
    x' <- UInt.wireU x
    UInt.assertGTE width x' (toInteger bound)
  ExprB (GTEU (ValU width bound) x) -> do
    x' <- UInt.wireU x
    UInt.assertLTE width x' (toInteger bound)
  ExprB (GTU x (ValU width bound)) -> do
    x' <- UInt.wireU x
    UInt.assertGT width x' (toInteger bound)
  ExprB (GTU (ValU width bound) x) -> do
    x' <- UInt.wireU x
    UInt.assertLT width x' (toInteger bound)
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
    writeValU out 1

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
  relateLC (RefFX a) result
assertEqF (VarFO a) (ValF b) = writeValF (RefFO a) b
assertEqF (VarFO a) (VarF b) = writeEqF (RefFO a) (RefFX b)
assertEqF (VarFO a) (VarFO b) = writeEqF (RefFO a) (RefFO b)
assertEqF (VarFO a) (VarFI b) = writeEqF (RefFO a) (RefFI b)
assertEqF (VarFO a) (VarFP b) = writeEqF (RefFO a) (RefFP b)
assertEqF (VarFO a) b = do
  result <- compileExprF b
  relateLC (RefFO a) result
assertEqF (VarFI a) (ValF b) = writeValF (RefFI a) b
assertEqF (VarFI a) (VarF b) = writeEqF (RefFI a) (RefFX b)
assertEqF (VarFI a) (VarFO b) = writeEqF (RefFI a) (RefFO b)
assertEqF (VarFI a) (VarFI b) = writeEqF (RefFI a) (RefFI b)
assertEqF (VarFI a) (VarFP b) = writeEqF (RefFI a) (RefFP b)
assertEqF (VarFI a) b = do
  result <- compileExprF b
  relateLC (RefFI a) result
assertEqF (VarFP a) (ValF b) = writeValF (RefFP a) b
assertEqF (VarFP a) (VarF b) = writeEqF (RefFP a) (RefFX b)
assertEqF (VarFP a) (VarFO b) = writeEqF (RefFP a) (RefFO b)
assertEqF (VarFP a) (VarFI b) = writeEqF (RefFP a) (RefFI b)
assertEqF (VarFP a) (VarFP b) = writeEqF (RefFP a) (RefFP b)
assertEqF (VarFP a) b = do
  result <- compileExprF b
  relateLC (RefFP a) result
assertEqF a b = do
  resultA <- compileExprF a
  resultB <- compileExprF b
  case (resultA, resultB) of
    (Constant valA, _) -> do
      assertLC valA resultB
    (Polynomial as, Constant valB) -> do
      assertLC valB (Polynomial as)
    (Polynomial as, Polynomial bs) -> do
      writeAddWithPolyL $ PolyL.merge as (PolyL.negate bs)

-- | Assert that two UInt expressions are equal
assertEqU :: (GaloisField n, Integral n) => ExprU n -> ExprU n -> M n ()
assertEqU (ValU _ a) (ValU _ b) = when (a /= b) $ throwError $ Error.ConflictingValuesU a b
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

--------------------------------------------------------------------------------

-- | Relates a RefF to a LC
relateLC :: (GaloisField n, Integral n) => RefF -> LC n -> M n ()
relateLC out (Constant val) = writeValF out val
relateLC out (Polynomial poly) = case PolyL.view poly of
  PolyL.RefMonomial 0 (x, 1) -> writeEq x (F out)
  PolyL.RefMonomial c (x, a) -> writeAdd c [(F out, -1), (x, a)]
  PolyL.RefBinomial c (x, a) (y, b) -> writeAdd c [(F out, -1), (x, a), (y, b)]
  PolyL.RefPolynomial c xs -> writeAdd c $ (F out, -1) : Map.toList xs
  _ -> return () -- TODO: dunno how to handle this yet

-- | Assign a value to a LC
assertLC :: (GaloisField n, Integral n) => n -> LC n -> M n ()
assertLC val (Constant val') =
  if val == val'
    then return ()
    else throwError $ Error.ConflictingValuesF val val'
assertLC val (Polynomial poly) = case PolyL.view poly of
  PolyL.RefMonomial c (x, a) ->
    -- c + ax = val => x = (val - c) / a
    writeVal x ((val - c) / a)
  PolyL.RefBinomial c (x, a) (y, b) ->
    -- val = c + ax + by
    writeAdd (c - val) [(x, a), (y, b)]
  PolyL.RefPolynomial c xs ->
    -- val = c + xs...
    writeAdd (c - val) (Map.toList xs)
  _ -> return () -- TODO: dunno how to handle this yet