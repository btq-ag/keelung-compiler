{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <&>" #-}

-- | Utilities for testing the compilation process:
--   * Functions ending with `WithOpts` expect the options
--   * Functions ending with `I` take the internal syntax as input
module Test.Util
  ( -- prints the compiled constraint module and R1CS
    debug,
    debugO0,
    debugI,
    debugO0I,
    debugWithOpts,
    debugWithOptsI,
    -- testing by cross-validating the interpreter and the solver
    check,
    checkO0,
    checkI,
    checkWithOpts,
    checkWithOptsI,
    -- for debugging the solver
    debugSolver,
    debugSolverWithOpts,
    -- constraint counting
    assertCount,
    assertCountI,
    assertCountO0,
    assertCountIO0,
    assertCountWithOpts,
    assertCountWithOptsI,
    -- helper functions
    compileAsConstraintModule,
    compileAsConstraintSystem,
    throwR1CS,
    throwErrorsWithOpts,
    throwErrors,
    gf181Info,
  )
where

import Data.Field.Galois
import Data.Proxy (Proxy (..))
import GHC.TypeLits
import Keelung hiding (Elaborated, compile)
import Keelung.Compiler (Error (..))
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.ConstraintModule (ConstraintModule)
import Keelung.Compiler.ConstraintSystem qualified as Compiler
import Keelung.Compiler.Linker.ReindexReport qualified as ReindexReport
import Keelung.Compiler.Options (Options)
import Keelung.Compiler.Options qualified as Options
import Keelung.Compiler.Util (gf181Info)
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Data.FieldInfo
import Keelung.Data.FieldInfo qualified as FieldInfo
import Keelung.Solver qualified as Solver
import Test.HUnit (assertFailure)
import Test.Hspec

--------------------------------------------------------------------------------

-- | Generate and test the report of variable reindexing
testReindexReportWithOpts :: (GaloisField n, Integral n) => Options -> Compiler.Internal n -> Either (Error n) (Maybe ReindexReport.Error)
testReindexReportWithOpts options syntax = do
  constraintModule <- Compiler.compileWithOptsI options syntax
  return $ ReindexReport.test constraintModule

--------------------------------------------------------------------------------

-- | Print the copmiled constraint module and R1CS
debugWithOptsI :: (GaloisField n, Integral n) => Options -> Compiler.Internal n -> IO ()
debugWithOptsI options syntax = do
  print $ fmap N <$> Compiler.compileWithOptsI options syntax
  print $ Compiler.compileWithOptsI options syntax >>= Compiler.link >>= return . fmap N

debugWithOpts :: (Encode t) => Options -> Comp t -> IO ()
debugWithOpts options program = caseFieldType fieldType handlePrime handleBinary
  where
    fieldType :: FieldType
    fieldType = FieldInfo.fieldTypeData (Options.optFieldInfo options)

    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      let options' = options {Options.optFieldInfo = fieldInfo}
      print (Compiler.compileWithOpts options' program :: Either (Error (N (Prime n))) (ConstraintModule (N (Prime n))))
      print (Compiler.compileWithOpts options' program >>= Compiler.link >>= Compiler.toR1CS :: Either (Error (N (Prime n))) (R1CS (N (Prime n))))
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      let options' = options {Options.optFieldInfo = fieldInfo}
      print (Compiler.compileWithOpts options' program :: Either (Error (N (Binary n))) (ConstraintModule (N (Binary n))))
      print (Compiler.compileWithOpts options' program >>= Compiler.link >>= Compiler.toR1CS :: Either (Error (N (Binary n))) (R1CS (N (Binary n))))

debug :: (Encode t) => FieldType -> Comp t -> IO ()
debug = debugWithOpts . Options.new

debugO0 :: (Encode t) => FieldType -> Comp t -> IO ()
debugO0 fieldType = debugWithOpts ((Options.new fieldType) {Options.optOptimize = False})

debugI :: (GaloisField n, Integral n) => FieldType -> Compiler.Internal n -> IO ()
debugI = debugWithOptsI . Options.new

debugO0I :: (GaloisField n, Integral n) => FieldType -> Compiler.Internal n -> IO ()
debugO0I fieldType = debugWithOptsI ((Options.new fieldType) {Options.optOptimize = False})

--------------------------------------------------------------------------------

-- | Accepts Internal syntax and check the result of compilation with the solver, for experimenting with new features not present in the language repo
checkWithOptsI :: (GaloisField n, Integral n) => Options -> Compiler.Internal n -> [Integer] -> [Integer] -> [Integer] -> IO ()
checkWithOptsI options syntax rawPublicInputs rawPrivateInputs expected = do
  -- tests for variable reindexing
  testReindexReportWithOpts options syntax `shouldBe` (Right Nothing :: Either (Error n) (Maybe ReindexReport.Error))
  -- constraint system solvers
  Compiler.solveWithOptsI options syntax rawPublicInputs rawPrivateInputs
    `shouldBe` (Right expected :: Either (Error n) [Integer])

checkI :: (GaloisField n, Integral n) => FieldType -> Compiler.Internal n -> [Integer] -> [Integer] -> [Integer] -> IO ()
checkI = checkWithOptsI . Options.new

--------------------------------------------------------------------------------

-- | Check the result of compilation with the interpreter and the solver
checkWithOpts :: (Encode t) => Options -> Comp t -> [Integer] -> [Integer] -> [Integer] -> IO ()
checkWithOpts options program rawPublicInputs rawPrivateInputs expected = caseFieldType fieldType handlePrime handleBinary
  where
    fieldType :: FieldType
    fieldType = FieldInfo.fieldTypeData (Options.optFieldInfo options)

    handlePrime :: (KnownNat n) => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      -- overwrite fieldInfo
      let options' = options {Options.optFieldInfo = fieldInfo}
      -- interpreter
      Compiler.interpret fieldInfo program rawPublicInputs rawPrivateInputs `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])
      -- tests for variable reindexing
      (Compiler.elaborateAndEncode program >>= Compiler.toInternalWithOpts options >>= testReindexReportWithOpts options') `shouldBe` (Right Nothing :: Either (Error (Prime n)) (Maybe ReindexReport.Error))
      -- constraint system solvers
      Compiler.solveWithOpts options' program rawPublicInputs rawPrivateInputs
        `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])

    handleBinary :: (KnownNat n) => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      -- overwrite fieldInfo
      let options' = options {Options.optFieldInfo = fieldInfo}
      -- interpreter
      Compiler.interpret fieldInfo program rawPublicInputs rawPrivateInputs `shouldBe` (Right expected :: Either (Error (Binary n)) [Integer])
      -- tests for variable reindexing
      (Compiler.elaborateAndEncode program >>= Compiler.toInternalWithOpts options >>= testReindexReportWithOpts options') `shouldBe` (Right Nothing :: Either (Error (Binary n)) (Maybe ReindexReport.Error))
      -- constraint system solvers
      Compiler.solveWithOpts options' program rawPublicInputs rawPrivateInputs
        `shouldBe` (Right expected :: Either (Error (Binary n)) [Integer])

check :: (Encode t) => FieldType -> Comp t -> [Integer] -> [Integer] -> [Integer] -> IO ()
check = checkWithOpts . Options.new

checkO0 :: (Encode t) => FieldType -> Comp t -> [Integer] -> [Integer] -> [Integer] -> IO ()
checkO0 fieldType = checkWithOpts ((Options.new fieldType) {Options.optOptimize = False})

--------------------------------------------------------------------------------

-- | Runs the solver and prints the log report for debugging
debugSolverWithOpts :: (Encode t) => Options -> Comp t -> [Integer] -> [Integer] -> IO ()
debugSolverWithOpts options program rawPublicInputs rawPrivateInputs = caseFieldType fieldType handlePrime handleBinary
  where
    fieldType = FieldInfo.fieldTypeData (Options.optFieldInfo options)

    handlePrime :: (KnownNat n) => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      let (err, logs) = Compiler.solveAndCollectLogWithOpts (options {Options.optFieldInfo = fieldInfo}) program rawPublicInputs rawPrivateInputs :: (Maybe (Error (Prime n)), Maybe (Solver.LogReport (Prime n)))
      mapM_ print err
      mapM_ print logs

    handleBinary :: (KnownNat n) => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      let (err, logs) = Compiler.solveAndCollectLogWithOpts (options {Options.optFieldInfo = fieldInfo}) program rawPublicInputs rawPrivateInputs :: (Maybe (Error (Binary n)), Maybe (Solver.LogReport (Binary n)))
      mapM_ print err
      mapM_ print logs

-- | Runs the solver and prints the log report for debugging with default options
debugSolver :: (Encode t) => FieldType -> Comp t -> [Integer] -> [Integer] -> IO ()
debugSolver = debugSolverWithOpts . Options.new

--------------------------------------------------------------------------

assertCountWithOptsI :: (GaloisField n, Integral n) => Options -> Compiler.Internal n -> Int -> IO ()
assertCountWithOptsI options syntax expected = do
  -- constraint system solvers
  case Compiler.compileWithOptsI options syntax >>= Compiler.link of
    Left err -> assertFailure (show err)
    Right cs -> Compiler.numberOfConstraints cs `shouldBe` expected

assertCountWithOpts :: (Encode t) => Options -> Comp t -> Int -> IO ()
assertCountWithOpts options program expected = caseFieldType (FieldInfo.fieldTypeData (Options.optFieldInfo options)) handlePrime handleBinary
  where
    handlePrime :: (KnownNat n) => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) _ = do
      case Compiler.elaborateAndEncode program >>= Compiler.toInternalWithOpts options of
        Left err -> assertFailure (show (err :: Error (Prime n)))
        Right syntax -> assertCountWithOptsI options (syntax :: Compiler.Internal (Prime n)) expected

    handleBinary :: (KnownNat n) => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) _ = do
      case Compiler.elaborateAndEncode program >>= Compiler.toInternalWithOpts options of
        Left err -> assertFailure (show (err :: Error (Binary n)))
        Right syntax -> assertCountWithOptsI options (syntax :: Compiler.Internal (Binary n)) expected

assertCountIO0 :: (GaloisField n, Integral n) => FieldType -> Compiler.Internal n -> Int -> IO ()
assertCountIO0 fieldType = assertCountWithOptsI ((Options.new fieldType) {Options.optOptimize = False})

assertCountO0 :: (Encode t) => FieldType -> Comp t -> Int -> IO ()
assertCountO0 fieldType = assertCountWithOpts ((Options.new fieldType) {Options.optOptimize = False})

assertCount :: (Encode t) => FieldType -> Comp t -> Int -> IO ()
assertCount = assertCountWithOpts . Options.new

assertCountI :: (GaloisField n, Integral n) => FieldType -> Compiler.Internal n -> Int -> IO ()
assertCountI fieldType = assertCountWithOptsI (Options.new fieldType)

--------------------------------------------------------------------------

-- | Utilities for testing

-- | Compile the program and return the constraint module
compileAsConstraintModule :: (Encode t, GaloisField n, Integral n) => FieldType -> Comp t -> IO (ConstraintModule n)
compileAsConstraintModule fieldType program = case Compiler.compile fieldType program of
  Left err -> assertFailure (show err)
  Right cm -> return cm

compileAsConstraintSystem :: (Encode t, GaloisField n, Integral n) => FieldType -> Comp t -> IO (Compiler.ConstraintSystem n)
compileAsConstraintSystem fieldType program = case Compiler.compile fieldType program >>= Compiler.link of
  Left err -> assertFailure (show err)
  Right cs -> return cs

-- | Expect R1CS interpreters to throw an error
throwR1CS :: (GaloisField n, Integral n, Encode t, Show t) => FieldType -> Comp t -> [Integer] -> [Integer] -> Error n -> IO ()
throwR1CS fieldType program rawPublicInputs rawPrivateInputs csError = do
  Compiler.solve fieldType program rawPublicInputs rawPrivateInputs
    `shouldBe` Left csError

throwErrorsWithOpts :: (GaloisField n, Integral n, Encode t, Show t) => Options -> Comp t -> [Integer] -> [Integer] -> Error n -> Error n -> IO ()
throwErrorsWithOpts options program rawPublicInputs rawPrivateInputs stError csError = caseFieldType fieldType handlePrime handleBinary
  where
    fieldType = FieldInfo.fieldTypeData (Options.optFieldInfo options)

    handlePrime :: (KnownNat n) => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      -- syntax tree interpreters
      Compiler.interpret fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left stError
      -- constraint system interpreters
      Compiler.solveWithOpts options program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError

    handleBinary :: (KnownNat n) => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      -- constraint system interpreters
      Compiler.interpret fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left stError
      -- constraint system interpreters
      Compiler.solveWithOpts options program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError

throwErrors :: (GaloisField n, Integral n, Encode t, Show t) => FieldType -> Comp t -> [Integer] -> [Integer] -> Error n -> Error n -> IO ()
throwErrors = throwErrorsWithOpts . Options.new
