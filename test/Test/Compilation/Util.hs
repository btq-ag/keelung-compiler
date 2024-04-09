{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Util
  ( -- prints the compiled constraint module and R1CS
    debugWithOpts,
    debug,
    debugO0,
    -- testing by comparing the interpreter and the solver
    testCompilerWithOpts,
    testCompiler,
    -- for debugging the solver
    debugSolverWithOpts,
    debugSolver,
    -- helper functions
    throwR1CS,
    throwErrorsWithOpts,
    throwErrors,
    assertSize,
    gf181Info,
  )
where

import Control.Arrow (left)
import Data.Field.Galois
import Data.Proxy (Proxy (..))
import GHC.TypeLits
import Keelung hiding (Elaborated, compile)
import Keelung.Compiler (Error (..), toR1CS)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.ConstraintModule (ConstraintModule)
import Keelung.Compiler.ConstraintSystem qualified as CS
import Keelung.Compiler.Linker.ReindexReport qualified as ReindexReport
import Keelung.Compiler.Options
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Compiler.Util (gf181Info)
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Data.FieldInfo
import Keelung.Interpreter qualified as Interpreter
import Keelung.Solver qualified as Solver
import Keelung.Syntax.Encode.Syntax qualified as Encoded
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
testReindexReportWithOpts :: (GaloisField n, Integral n, Encode t) => Options -> Comp t -> Either (Error n) (Maybe ReindexReport.Error)
testReindexReportWithOpts options prog = do
  elab <- Compiler.elaborateAndEncode prog
  constraintModule <- Compiler.compileElabWithOpts options elab
  return $ ReindexReport.test constraintModule

--------------------------------------------------------------------------------

-- | Print the copmiled constraint module and R1CS
debugWithOpts :: (Encode t) => Options -> FieldType -> Comp t -> IO ()
debugWithOpts options fieldType program = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      let options' = options {optFieldInfo = fieldInfo}
      print (Compiler.compileWithOpts options' program :: Either (Error (N (Prime n))) (ConstraintModule (N (Prime n))))
      print (toR1CS <$> Compiler.compileAndLinkWithOpts options' program :: Either (Error (N (Prime n))) (R1CS (N (Prime n))))
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      let options' = options {optFieldInfo = fieldInfo}
      print (Compiler.compileWithOpts options' program :: Either (Error (N (Binary n))) (ConstraintModule (N (Binary n))))
      print (toR1CS <$> Compiler.compileAndLinkWithOpts options' program :: Either (Error (N (Binary n))) (R1CS (N (Binary n))))

debug :: (Encode t) => FieldType -> Comp t -> IO ()
debug = debugWithOpts defaultOptions

debugO0 :: (Encode t) => FieldType -> Comp t -> IO ()
debugO0 = debugWithOpts (defaultOptions {optOptimize = False})

--------------------------------------------------------------------------------

-- | Use the interpreter to check the result of compilation + witness generation
testCompilerWithOpts :: (Encode t) => Options -> FieldType -> Comp t -> [Integer] -> [Integer] -> [Integer] -> IO ()
testCompilerWithOpts options fieldType program rawPublicInputs rawPrivateInputs expected = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime :: (KnownNat n) => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      -- overwrite fieldInfo
      let options' = options {optFieldInfo = fieldInfo}
      -- interpreter
      interpretSyntaxTree fieldInfo program rawPublicInputs rawPrivateInputs `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])
      -- tests for variable reindexing
      testReindexReportWithOpts options' program `shouldBe` (Right Nothing :: Either (Error (Prime n)) (Maybe ReindexReport.Error))
      -- constraint system solvers
      Compiler.solveOutputWithOpts options' program rawPublicInputs rawPrivateInputs
        `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])

    handleBinary :: (KnownNat n) => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      -- overwrite fieldInfo
      let options' = options {optFieldInfo = fieldInfo}
      -- interpreter
      interpretSyntaxTree fieldInfo program rawPublicInputs rawPrivateInputs `shouldBe` (Right expected :: Either (Error (Binary n)) [Integer])
      -- tests for variable reindexing
      testReindexReportWithOpts options' program `shouldBe` (Right Nothing :: Either (Error (Binary n)) (Maybe ReindexReport.Error))
      -- constraint system solvers
      Compiler.solveOutputWithOpts options' program rawPublicInputs rawPrivateInputs
        `shouldBe` (Right expected :: Either (Error (Binary n)) [Integer])

testCompiler :: (Encode t) => FieldType -> Comp t -> [Integer] -> [Integer] -> [Integer] -> IO ()
testCompiler = testCompilerWithOpts defaultOptions

--------------------------------------------------------------------------------

-- | Runs the solver and prints the log report for debugging
debugSolverWithOpts :: (Encode t) => Options -> FieldType -> Comp t -> [Integer] -> [Integer] -> IO ()
debugSolverWithOpts options fieldType program rawPublicInputs rawPrivateInputs = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime :: (KnownNat n) => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      let (err, logs) = Compiler.solveOutputAndCollectLogWithOpts (options {optFieldInfo = fieldInfo}) program rawPublicInputs rawPrivateInputs :: (Maybe (Error (Prime n)), Maybe (Solver.LogReport (Prime n)))
      mapM_ print err
      mapM_ print logs

    handleBinary :: (KnownNat n) => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      let (err, logs) = Compiler.solveOutputAndCollectLogWithOpts (options {optFieldInfo = fieldInfo}) program rawPublicInputs rawPrivateInputs :: (Maybe (Error (Binary n)), Maybe (Solver.LogReport (Binary n)))
      mapM_ print err
      mapM_ print logs

-- | Runs the solver and prints the log report for debugging with default options
debugSolver :: (Encode t) => FieldType -> Comp t -> [Integer] -> [Integer] -> IO ()
debugSolver = debugSolverWithOpts defaultOptions

--------------------------------------------------------------------------

-- | Utilities for testing

-- | Expect R1CS interpreters to throw an error
throwR1CS :: (GaloisField n, Integral n, Encode t, Show t) => FieldType -> Comp t -> [Integer] -> [Integer] -> Error n -> IO ()
throwR1CS fieldType program rawPublicInputs rawPrivateInputs csError = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime :: (KnownNat n) => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      -- syntax tree interpreters
      -- interpretSyntaxTree fieldInfo program rawPublicInputs rawPrivateInputs
      --   `shouldBe` Left (InterpreterError stError)
      -- constraint system interpreters
      Compiler.solveOutput fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError
      Compiler.solveOutputO0 fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError

    handleBinary :: (KnownNat n) => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      -- constraint system interpreters
      -- interpretSyntaxTree fieldInfo program rawPublicInputs rawPrivateInputs
      --   `shouldBe` Left (InterpreterError stError)
      -- constraint system interpreters
      Compiler.solveOutput fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError
      Compiler.solveOutputO0 fieldInfo program rawPublicInputs rawPrivateInputs
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
      Compiler.solveOutputWithOpts options' program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError

    handleBinary :: (KnownNat n) => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      -- overwrite fieldInfo
      let options' = options {optFieldInfo = fieldInfo}
      -- constraint system interpreters
      interpretSyntaxTree fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left stError
      -- constraint system interpreters
      Compiler.solveOutputWithOpts options' program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError

throwErrors :: (GaloisField n, Integral n, Encode t, Show t) => FieldType -> Comp t -> [Integer] -> [Integer] -> Error n -> Error n -> IO ()
throwErrors = throwErrorsWithOpts defaultOptions

assertSize :: (Encode t) => Int -> Comp t -> IO ()
assertSize afterSize program = do
  case Compiler.asGF181N (Compiler.compileAndLink gf181Info program) of
    Left err -> print err
    Right cs -> do
      CS.numberOfConstraints cs `shouldBe` afterSize
