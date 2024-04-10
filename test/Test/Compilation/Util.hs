{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Utilities for testing the compilation process:
--   * Functions ending with `WithOpts` expect the options
--   * Functions ending with `I` take the internal syntax as input
module Test.Compilation.Util
  ( -- prints the compiled constraint module and R1CS
    debugWithOpts,
    debug,
    -- testing by comparing the interpreter and the solver
    validateWithOpts,
    validate,
    -- like `validate`, but accepts the internal syntax and without the interpreter
    validateWithOptsI,
    validateI,
    -- for debugging the solver
    debugSolverWithOpts,
    debugSolver,
    -- constraint counting
    assertCountWithOptsI,
    assertCountWithOpts,
    assertCount,
    -- helper functions
    throwR1CS,
    throwErrorsWithOpts,
    throwErrors,
    gf181Info,
  )
where

import Control.Arrow (left)
import Data.Field.Galois
import Data.Proxy (Proxy (..))
import GHC.TypeLits
import Keelung hiding (Elaborated, compile)
import Keelung.Compiler (Error (..))
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.ConstraintModule (ConstraintModule)
import Keelung.Compiler.ConstraintSystem qualified as Compiler
import Keelung.Compiler.Linker.ReindexReport qualified as ReindexReport
import Keelung.Compiler.Options
import Keelung.Compiler.Options qualified as Options
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Compiler.Syntax.ToInternal qualified as ToInternal
import Keelung.Compiler.Util (gf181Info)
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Data.FieldInfo
import Keelung.Data.FieldInfo qualified as FieldInfo
import Keelung.Interpreter qualified as Interpreter
import Keelung.Solver qualified as Solver
import Keelung.Syntax.Encode.Syntax qualified as Encoded
import Test.HUnit (assertFailure)
import Test.Hspec

--------------------------------------------------------------------------------

-- | syntax tree interpreter
interpretSyntaxTree :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> Either (Error n) [Integer]
interpretSyntaxTree fieldInfo prog rawPublicInputs rawPrivateInputs = do
  elab <- Compiler.elaborateAndEncode prog
  inputs <- left InputError (Inputs.deserialize (Encoded.compCounters (Encoded.elabComp elab)) rawPublicInputs rawPrivateInputs)
  left InterpreterError (Interpreter.run fieldInfo elab inputs)

--------------------------------------------------------------------------------

-- | Generate and test the report of variable reindexing
testReindexReportWithOpts :: (GaloisField n, Integral n) => Options -> Compiler.Internal n -> Either (Error n) (Maybe ReindexReport.Error)
testReindexReportWithOpts options syntax = do
  constraintModule <- Compiler.compileWithOptsI options syntax
  return $ ReindexReport.test constraintModule

--------------------------------------------------------------------------------

-- | Print the copmiled constraint module and R1CS
debugWithOpts :: (Encode t) => Options -> FieldType -> Comp t -> IO ()
debugWithOpts options fieldType program = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      let options' = options {optFieldInfo = fieldInfo}
      print (Compiler.compileWithOpts options' program :: Either (Error (N (Prime n))) (ConstraintModule (N (Prime n))))
      print (Compiler.compileWithOpts options' program >>= Compiler.link >>= Compiler.toR1CS :: Either (Error (N (Prime n))) (R1CS (N (Prime n))))
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      let options' = options {optFieldInfo = fieldInfo}
      print (Compiler.compileWithOpts options' program :: Either (Error (N (Binary n))) (ConstraintModule (N (Binary n))))
      print (Compiler.compileWithOpts options' program >>= Compiler.link >>= Compiler.toR1CS :: Either (Error (N (Binary n))) (R1CS (N (Binary n))))

debug :: (Encode t) => FieldType -> Comp t -> IO ()
debug = debugWithOpts defaultOptions

--------------------------------------------------------------------------------

-- | Accepts Internal syntax and check the result of compilation with the solver, for experimenting with new features not present in the language repo
validateWithOptsI :: (GaloisField n, Integral n) => Options -> Compiler.Internal n -> [Integer] -> [Integer] -> [Integer] -> IO ()
validateWithOptsI options syntax rawPublicInputs rawPrivateInputs expected = do
  -- tests for variable reindexing
  testReindexReportWithOpts options syntax `shouldBe` (Right Nothing :: Either (Error n) (Maybe ReindexReport.Error))
  -- constraint system solvers
  Compiler.solveWithOptsI options syntax rawPublicInputs rawPrivateInputs
    `shouldBe` (Right expected :: Either (Error n) [Integer])

validateI :: (GaloisField n, Integral n) => Compiler.Internal n -> [Integer] -> [Integer] -> [Integer] -> IO ()
validateI = validateWithOptsI defaultOptions

--------------------------------------------------------------------------------

-- | Check the result of compilation with the interpreter and the solver
validateWithOpts :: (Encode t) => Options -> FieldType -> Comp t -> [Integer] -> [Integer] -> [Integer] -> IO ()
validateWithOpts options fieldType program rawPublicInputs rawPrivateInputs expected = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime :: (KnownNat n) => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      -- overwrite fieldInfo
      let options' = options {optFieldInfo = fieldInfo}
      -- interpreter
      interpretSyntaxTree fieldInfo program rawPublicInputs rawPrivateInputs `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])
      -- tests for variable reindexing
      (Compiler.elaborateAndEncode program >>= testReindexReportWithOpts options' . ToInternal.run (optFieldInfo options)) `shouldBe` (Right Nothing :: Either (Error (Prime n)) (Maybe ReindexReport.Error))
      -- constraint system solvers
      Compiler.solveWithOpts options' program rawPublicInputs rawPrivateInputs
        `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])

    handleBinary :: (KnownNat n) => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      -- overwrite fieldInfo
      let options' = options {optFieldInfo = fieldInfo}
      -- interpreter
      interpretSyntaxTree fieldInfo program rawPublicInputs rawPrivateInputs `shouldBe` (Right expected :: Either (Error (Binary n)) [Integer])
      -- tests for variable reindexing
      (Compiler.elaborateAndEncode program >>= testReindexReportWithOpts options' . ToInternal.run (optFieldInfo options)) `shouldBe` (Right Nothing :: Either (Error (Binary n)) (Maybe ReindexReport.Error))
      -- constraint system solvers
      Compiler.solveWithOpts options' program rawPublicInputs rawPrivateInputs
        `shouldBe` (Right expected :: Either (Error (Binary n)) [Integer])

validate :: (Encode t) => FieldType -> Comp t -> [Integer] -> [Integer] -> [Integer] -> IO ()
validate = validateWithOpts defaultOptions

--------------------------------------------------------------------------------

-- | Runs the solver and prints the log report for debugging
-- debugSolverWithOptsI :: (GaloisField n, Integral n) => Options -> Compiler.Internal n -> [Integer] -> [Integer] -> IO ()
-- debugSolverWithOptsI options syntax rawPublicInputs rawPrivateInputs = do
--   -- constraint system solvers
--   case Compiler.linkConstraintModule <$> Compiler.compileWithOptsI options syntax of
--     Left err -> assertFailure (show err)
--     Right cs -> Compiler.numberOfConstraints cs `shouldBe` expected
debugSolverWithOpts :: (Encode t) => Options -> FieldType -> Comp t -> [Integer] -> [Integer] -> IO ()
debugSolverWithOpts options fieldType program rawPublicInputs rawPrivateInputs = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime :: (KnownNat n) => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      let (err, logs) = Compiler.solveAndCollectLogWithOpts (options {optFieldInfo = fieldInfo}) program rawPublicInputs rawPrivateInputs :: (Maybe (Error (Prime n)), Maybe (Solver.LogReport (Prime n)))
      mapM_ print err
      mapM_ print logs

    handleBinary :: (KnownNat n) => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      let (err, logs) = Compiler.solveAndCollectLogWithOpts (options {optFieldInfo = fieldInfo}) program rawPublicInputs rawPrivateInputs :: (Maybe (Error (Binary n)), Maybe (Solver.LogReport (Binary n)))
      mapM_ print err
      mapM_ print logs

-- | Runs the solver and prints the log report for debugging with default options
debugSolver :: (Encode t) => FieldType -> Comp t -> [Integer] -> [Integer] -> IO ()
debugSolver = debugSolverWithOpts defaultOptions

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
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      case ToInternal.run fieldInfo <$> Compiler.elaborateAndEncode program of
        Left err -> assertFailure (show (err :: Error (Prime n)))
        Right syntax -> assertCountWithOptsI options (syntax :: Compiler.Internal (Prime n)) expected

    handleBinary :: (KnownNat n) => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      case ToInternal.run fieldInfo <$> Compiler.elaborateAndEncode program of
        Left err -> assertFailure (show (err :: Error (Binary n)))
        Right syntax -> assertCountWithOptsI options (syntax :: Compiler.Internal (Binary n)) expected

assertCount :: (Encode t) => FieldType -> Comp t -> Int -> IO ()
assertCount = assertCountWithOpts . Options.new

--------------------------------------------------------------------------

-- | Utilities for testing

-- | Expect R1CS interpreters to throw an error
throwR1CS :: (GaloisField n, Integral n, Encode t, Show t) => FieldType -> Comp t -> [Integer] -> [Integer] -> Error n -> IO ()
throwR1CS fieldType program rawPublicInputs rawPrivateInputs csError = do
  Compiler.solve fieldType program rawPublicInputs rawPrivateInputs
    `shouldBe` Left csError

throwErrorsWithOpts :: (GaloisField n, Integral n, Encode t, Show t) => Options -> FieldType -> Comp t -> [Integer] -> [Integer] -> Error n -> Error n -> IO ()
throwErrorsWithOpts options fieldType program rawPublicInputs rawPrivateInputs stError csError = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime :: (KnownNat n) => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      -- overwrite fieldInfo
      let options' = options {optFieldInfo = fieldInfo}
      -- syntax tree interpreters
      interpretSyntaxTree fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left stError
      -- constraint system interpreters
      Compiler.solveWithOpts options' program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError

    handleBinary :: (KnownNat n) => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      -- overwrite fieldInfo
      let options' = options {optFieldInfo = fieldInfo}
      -- constraint system interpreters
      interpretSyntaxTree fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left stError
      -- constraint system interpreters
      Compiler.solveWithOpts options' program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError

throwErrors :: (GaloisField n, Integral n, Encode t, Show t) => FieldType -> Comp t -> [Integer] -> [Integer] -> Error n -> Error n -> IO ()
throwErrors = throwErrorsWithOpts defaultOptions
