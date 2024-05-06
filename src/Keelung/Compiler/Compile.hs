{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile (run) where

import Control.Arrow (left)
import Control.Monad.Except
import Control.Monad.RWS
import Data.Field.Galois (GaloisField)
import Data.Map.Strict qualified as Map
import Keelung.Compiler.Compile.Boolean qualified as Boolean
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.Field qualified as Field
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Compile.UInt qualified as UInt
import Keelung.Compiler.ConstraintModule
import Keelung.Compiler.Error
import Keelung.Compiler.Options
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.FieldInfo qualified as FieldInfo
import Keelung.Data.LC (LC (..), neg, (@))
import Keelung.Data.LC qualified as LC
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.Slice qualified as Slice
import Keelung.Syntax (widthOf)

--------------------------------------------------------------------------------

-- | Compile an untyped expression to a constraint system
run :: (GaloisField n, Integral n) => Options -> Internal n -> Either (Error n) (ConstraintModule n)
run options (Internal untypedExprs _ counters assertions sideEffects) = left CompilerError $ runM options bootstrapCompilers counters $ do
  forM_ untypedExprs $ \(var, expr) -> do
    case expr of
      ExprB x -> do
        let out = RefBO var
        result <- compileExprB x
        case result of
          Left var' -> writeRefBEq out var'
          Right val -> writeRefBVal out val
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
    Left var' -> writeRefBEq (RefBX var) var'
    Right val' -> writeRefBVal (RefBX var) val'
compileSideEffect (AssignmentF var val) = do
  result <- compileExprF val
  relateLC (RefFX var) result
compileSideEffect (AssignmentU width var val) = compileExprU (RefUX width var) val
compileSideEffect (ToField width varU varF) = do
  fieldWidth <- gets (FieldInfo.fieldWidth . optFieldInfo . cmOptions)
  -- only convert the Slice of length "width `min` fieldWidth" to a RefF because that's the maximum width allowed by a RefF
  let slice = Slice.Slice (RefUX width varU) 0 (width `min` fieldWidth)
  writeAdd 0 [(F (RefFX varF), -1)] [(slice, 1)]
compileSideEffect (ToUInt width varU varF) = do
  fieldWidth <- gets (FieldInfo.fieldWidth . optFieldInfo . cmOptions)
  -- represent "varU" as the sum of 2 Slices
  let actualWidth = width `min` fieldWidth
  let toF = Slice.Slice (RefUX width varU) 0 actualWidth
  let rest = Slice.Slice (RefUX width varU) actualWidth width
  -- varF = toF + 2^actualWidth * rest
  writeAdd 0 [(F (RefFX varF), -1)] [(toF, 1), (rest, 2 ^ actualWidth)]
  -- rest = 0
  writeSliceVal rest 0
compileSideEffect (BitsToUInt width varU bits) = do
  let refU = RefUX width varU

  -- pair variables with slices, such that
  --    var0 + 2var1 + ... + 2^(width-1)var(width-1) = slice
  -- we may need multiple pairs because of the field size limitation
  -- each pair can only has at most `fieldWidth - 1` variables
  fieldInfo <- gets (optFieldInfo . cmOptions)
  let fieldWidth = FieldInfo.fieldWidth fieldInfo

  polys <- step fieldWidth bits
  let slices = LC.fromRefU fieldInfo (Left refU)
  forM_ (zip polys slices) $ \(a, b) -> do
    writeAddWithLC $ neg a <> b
  where
    step :: (GaloisField n, Integral n) => Width -> [ExprB n] -> M n [LC n]
    step _ [] = return []
    step fieldWidth exprsss = do
      let (exprs, exprss) = splitAt fieldWidth exprsss
      poly <-
        foldM
          ( \acc (i, expr) -> do
              result <- compileExprB expr
              return $ case result of
                Left var -> acc <> (2 ^ (i :: Int)) @ B var
                Right val -> acc <> Constant (if val then 2 ^ i else 0)
          )
          mempty
          (zip [0 ..] exprs)

      polys <- step fieldWidth exprss

      return (poly : polys)
compileSideEffect (DivMod width dividend divisor quotient remainder) = do
  d <- wireU dividend
  v <- wireU divisor
  q <- wireU quotient
  r <- wireU remainder
  UInt.assert width d v q r
compileSideEffect (CLDivMod width dividend divisor quotient remainder) = do
  d <- wireU dividend
  v <- wireU divisor
  q <- wireU quotient
  r <- wireU remainder
  UInt.assertCL width d v q r
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
  ExprB (LTEU x (ValU bound)) -> do
    x' <- UInt.wireU x
    UInt.assertLTE (widthOf bound) x' (toInteger bound)
  ExprB (LTEU (ValU bound) x) -> do
    x' <- UInt.wireU x
    UInt.assertGTE (widthOf bound) x' (toInteger bound)
  ExprB (LTU x (ValU bound)) -> do
    x' <- UInt.wireU x
    UInt.assertLT (widthOf bound) x' (toInteger bound)
  ExprB (LTU (ValU bound) x) -> do
    x' <- UInt.wireU x
    UInt.assertGT (widthOf bound) x' (toInteger bound)
  ExprB (GTEU x (ValU bound)) -> do
    x' <- UInt.wireU x
    UInt.assertGTE (widthOf bound) x' (toInteger bound)
  ExprB (GTEU (ValU bound) x) -> do
    x' <- UInt.wireU x
    UInt.assertLTE (widthOf bound) x' (toInteger bound)
  ExprB (GTU x (ValU bound)) -> do
    x' <- UInt.wireU x
    UInt.assertGT (widthOf bound) x' (toInteger bound)
  ExprB (GTU (ValU bound) x) -> do
    x' <- UInt.wireU x
    UInt.assertLT (widthOf bound) x' (toInteger bound)
  ExprB x -> do
    -- out <- freshRefB
    result <- compileExprB x
    case result of
      Left var -> writeRefBVal var True
      Right True -> return ()
      Right val -> throwError $ Error.ConflictingValuesB True val
  ExprF x -> do
    result <- compileExprF x
    assertLC 1 result
  ExprU x -> do
    let width = widthOf x
    out <- freshRefU width
    compileExprU out x
    writeRefUVal out 1

-- | Assert that two Boolean expressions are equal
assertEqB :: (GaloisField n, Integral n) => ExprB n -> ExprB n -> M n ()
assertEqB (ValB a) (ValB b) = when (a /= b) $ throwError $ Error.ConflictingValuesB a b
assertEqB (ValB a) (VarB b) = writeRefBVal (RefBX b) a
assertEqB (ValB a) (VarBO b) = writeRefBVal (RefBO b) a
assertEqB (ValB a) (VarBI b) = writeRefBVal (RefBI b) a
assertEqB (ValB a) (VarBP b) = writeRefBVal (RefBP b) a
assertEqB (ValB a) b = do
  result <- compileExprB b
  case result of
    Left var -> writeRefBVal var a
    Right val -> when (a /= val) $ throwError $ Error.ConflictingValuesB a val
assertEqB (VarB a) (ValB b) = writeRefBVal (RefBX a) b
assertEqB (VarB a) (VarB b) = writeRefBEq (RefBX a) (RefBX b)
assertEqB (VarB a) (VarBO b) = writeRefBEq (RefBX a) (RefBO b)
assertEqB (VarB a) (VarBI b) = writeRefBEq (RefBX a) (RefBI b)
assertEqB (VarB a) (VarBP b) = writeRefBEq (RefBX a) (RefBP b)
assertEqB (VarB a) b = do
  result <- compileExprB b
  case result of
    Left var -> writeRefBEq (RefBX a) var
    Right val -> writeRefBVal (RefBX a) val
assertEqB (VarBO a) (ValB b) = writeRefBVal (RefBO a) b
assertEqB (VarBO a) (VarB b) = writeRefBEq (RefBO a) (RefBX b)
assertEqB (VarBO a) (VarBO b) = writeRefBEq (RefBO a) (RefBO b)
assertEqB (VarBO a) (VarBI b) = writeRefBEq (RefBO a) (RefBI b)
assertEqB (VarBO a) (VarBP b) = writeRefBEq (RefBO a) (RefBP b)
assertEqB (VarBO a) b = do
  result <- compileExprB b
  case result of
    Left var -> writeRefBEq (RefBO a) var
    Right val -> writeRefBVal (RefBO a) val
assertEqB (VarBI a) (ValB b) = writeRefBVal (RefBI a) b
assertEqB (VarBI a) (VarB b) = writeRefBEq (RefBI a) (RefBX b)
assertEqB (VarBI a) (VarBO b) = writeRefBEq (RefBI a) (RefBO b)
assertEqB (VarBI a) (VarBI b) = writeRefBEq (RefBI a) (RefBI b)
assertEqB (VarBI a) (VarBP b) = writeRefBEq (RefBI a) (RefBP b)
assertEqB (VarBI a) b = do
  result <- compileExprB b
  case result of
    Left var -> writeRefBEq (RefBI a) var
    Right val -> writeRefBVal (RefBI a) val
assertEqB (VarBP a) (ValB b) = writeRefBVal (RefBP a) b
assertEqB (VarBP a) (VarB b) = writeRefBEq (RefBP a) (RefBX b)
assertEqB (VarBP a) (VarBO b) = writeRefBEq (RefBP a) (RefBO b)
assertEqB (VarBP a) (VarBI b) = writeRefBEq (RefBP a) (RefBI b)
assertEqB (VarBP a) (VarBP b) = writeRefBEq (RefBP a) (RefBP b)
assertEqB (VarBP a) b = do
  result <- compileExprB b
  case result of
    Left var -> writeRefBEq (RefBI a) var
    Right val -> writeRefBVal (RefBI a) val
assertEqB a b = do
  a' <- compileExprB a
  b' <- compileExprB b
  case (a', b') of
    (Left varA, Left varB) -> writeRefBEq varA varB
    (Left varA, Right valB) -> writeRefBVal varA valB
    (Right valA, Left varB) -> writeRefBVal varB valA
    (Right valA, Right valB) -> when (valA /= valB) $ throwError $ Error.ConflictingValuesB valA valB

-- | Assert that two Field expressions are equal
assertEqF :: (GaloisField n, Integral n) => ExprF n -> ExprF n -> M n ()
assertEqF (ValF a) (ValF b) = when (a /= b) $ throwError $ Error.ConflictingValuesF a b
assertEqF (ValF a) (VarF b) = writeRefFVal (RefFX b) a
assertEqF (ValF a) (VarFO b) = writeRefFVal (RefFO b) a
assertEqF (ValF a) (VarFI b) = writeRefFVal (RefFI b) a
assertEqF (ValF a) (VarFP b) = writeRefFVal (RefFP b) a
assertEqF (ValF a) b = do
  result <- compileExprF b
  assertLC a result
assertEqF (VarF a) (ValF b) = writeRefFVal (RefFX a) b
assertEqF (VarF a) (VarF b) = writeRefFEq (RefFX a) (RefFX b)
assertEqF (VarF a) (VarFO b) = writeRefFEq (RefFX a) (RefFO b)
assertEqF (VarF a) (VarFI b) = writeRefFEq (RefFX a) (RefFI b)
assertEqF (VarF a) (VarFP b) = writeRefFEq (RefFX a) (RefFP b)
assertEqF (VarF a) b = do
  result <- compileExprF b
  relateLC (RefFX a) result
assertEqF (VarFO a) (ValF b) = writeRefFVal (RefFO a) b
assertEqF (VarFO a) (VarF b) = writeRefFEq (RefFO a) (RefFX b)
assertEqF (VarFO a) (VarFO b) = writeRefFEq (RefFO a) (RefFO b)
assertEqF (VarFO a) (VarFI b) = writeRefFEq (RefFO a) (RefFI b)
assertEqF (VarFO a) (VarFP b) = writeRefFEq (RefFO a) (RefFP b)
assertEqF (VarFO a) b = do
  result <- compileExprF b
  relateLC (RefFO a) result
assertEqF (VarFI a) (ValF b) = writeRefFVal (RefFI a) b
assertEqF (VarFI a) (VarF b) = writeRefFEq (RefFI a) (RefFX b)
assertEqF (VarFI a) (VarFO b) = writeRefFEq (RefFI a) (RefFO b)
assertEqF (VarFI a) (VarFI b) = writeRefFEq (RefFI a) (RefFI b)
assertEqF (VarFI a) (VarFP b) = writeRefFEq (RefFI a) (RefFP b)
assertEqF (VarFI a) b = do
  result <- compileExprF b
  relateLC (RefFI a) result
assertEqF (VarFP a) (ValF b) = writeRefFVal (RefFP a) b
assertEqF (VarFP a) (VarF b) = writeRefFEq (RefFP a) (RefFX b)
assertEqF (VarFP a) (VarFO b) = writeRefFEq (RefFP a) (RefFO b)
assertEqF (VarFP a) (VarFI b) = writeRefFEq (RefFP a) (RefFI b)
assertEqF (VarFP a) (VarFP b) = writeRefFEq (RefFP a) (RefFP b)
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
    (Polynomial _, Polynomial _) -> do
      writeAddWithLC $ resultA <> neg resultB

-- | Assert that two UInt expressions are equal
assertEqU :: (GaloisField n, Integral n) => ExprU n -> ExprU n -> M n ()
assertEqU (ValU a) (ValU b) = when (a /= b) $ throwError $ Error.ConflictingValuesU (toInteger a) (toInteger b)
assertEqU (ValU a) (VarU w b) = writeRefUVal (RefUX w b) a
assertEqU (ValU a) (VarUO w b) = writeRefUVal (RefUO w b) a
assertEqU (ValU a) (VarUI w b) = writeRefUVal (RefUI w b) a
assertEqU (ValU a) (VarUP w b) = writeRefUVal (RefUP w b) a
assertEqU (ValU a) b = do
  out <- freshRefU (widthOf a)
  compileExprU out b
  writeRefUVal out a
assertEqU (VarU w a) (ValU b) = writeRefUVal (RefUX w a) b
assertEqU (VarU w a) (VarU _ b) = writeRefUEq (RefUX w a) (RefUX w b)
assertEqU (VarU w a) (VarUO _ b) = writeRefUEq (RefUX w a) (RefUO w b)
assertEqU (VarU w a) (VarUI _ b) = writeRefUEq (RefUX w a) (RefUI w b)
assertEqU (VarU w a) (VarUP _ b) = writeRefUEq (RefUX w a) (RefUP w b)
assertEqU (VarU w a) b = do
  out <- freshRefU w
  compileExprU out b
  writeRefUEq (RefUX w a) out
assertEqU (VarUO w a) (ValU b) = writeRefUVal (RefUO w a) b
assertEqU (VarUO w a) (VarU _ b) = writeRefUEq (RefUO w a) (RefUX w b)
assertEqU (VarUO w a) (VarUO _ b) = writeRefUEq (RefUO w a) (RefUO w b)
assertEqU (VarUO w a) (VarUI _ b) = writeRefUEq (RefUO w a) (RefUI w b)
assertEqU (VarUO w a) (VarUP _ b) = writeRefUEq (RefUO w a) (RefUP w b)
assertEqU (VarUO w a) b = do
  out <- freshRefU w
  compileExprU out b
  writeRefUEq (RefUO w a) out
assertEqU (VarUI w a) (ValU b) = writeRefUVal (RefUI w a) b
assertEqU (VarUI w a) (VarU _ b) = writeRefUEq (RefUI w a) (RefUX w b)
assertEqU (VarUI w a) (VarUO _ b) = writeRefUEq (RefUI w a) (RefUO w b)
assertEqU (VarUI w a) (VarUI _ b) = writeRefUEq (RefUI w a) (RefUI w b)
assertEqU (VarUI w a) (VarUP _ b) = writeRefUEq (RefUI w a) (RefUP w b)
assertEqU (VarUI w a) b = do
  out <- freshRefU w
  compileExprU out b
  writeRefUEq (RefUI w a) out
assertEqU (VarUP w a) (ValU b) = writeRefUVal (RefUP w a) b
assertEqU (VarUP w a) (VarU _ b) = writeRefUEq (RefUP w a) (RefUX w b)
assertEqU (VarUP w a) (VarUO _ b) = writeRefUEq (RefUP w a) (RefUO w b)
assertEqU (VarUP w a) (VarUI _ b) = writeRefUEq (RefUP w a) (RefUI w b)
assertEqU (VarUP w a) (VarUP _ b) = writeRefUEq (RefUP w a) (RefUP w b)
assertEqU (VarUP w a) b = do
  out <- freshRefU w
  compileExprU out b
  writeRefUEq (RefUP w a) out
assertEqU a b = do
  let width = widthOf a
  a' <- freshRefU width
  b' <- freshRefU width
  compileExprU a' a
  compileExprU b' b
  writeRefUEq a' b'

--------------------------------------------------------------------------------

-- | Relates a RefF to a LC
relateLC :: (GaloisField n, Integral n) => RefF -> LC n -> M n ()
relateLC out (Constant val) = writeRefFVal out val
relateLC out (Polynomial poly) = case PolyL.view poly of
  PolyL.RefMonomial 0 (x, 1) -> writeRefEq x (F out)
  PolyL.RefMonomial c (x, a) -> writeAdd c [(F out, -1), (x, a)] []
  PolyL.RefBinomial c (x, a) (y, b) -> writeAdd c [(F out, -1), (x, a), (y, b)] []
  PolyL.RefPolynomial c xs -> writeAdd c ((F out, -1) : Map.toList xs) []
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
    writeRefVal x ((val - c) / a)
  PolyL.RefBinomial c (x, a) (y, b) ->
    -- val = c + ax + by
    writeAdd (c - val) [(x, a), (y, b)] []
  PolyL.RefPolynomial c xs ->
    -- val = c + xs...
    writeAdd (c - val) (Map.toList xs) []
  _ -> return () -- TODO: dunno how to handle this yet