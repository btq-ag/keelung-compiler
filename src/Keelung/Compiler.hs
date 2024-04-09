-- | Top level functions for everything?
module Keelung.Compiler
  ( module Keelung.Compiler.Error,
    GaloisField,
    Semiring (one, zero),
    module Prelude,
    ConstraintSystem (..),
    Internal (..),
    module Keelung.Compiler.R1CS,
    -- interpret
    interpretElab,
    interpret,
    -- compile to ConstraintModule
    compileInternalWithOpts,
    compileElabWithOpts,
    compileWithOpts,
    compileO0Elab,
    compileO1Elab,
    -- compile and link to ConstraintSystem
    compileAndLinkWithOpts,
    compileAndLink,
    -- generate witness
    generateWitnessElab,
    generateWitness,
    -- solve R1CS and return output
    solveOutputElabWithOpts,
    solveOutputWithOpts,
    solveOutput,
    solveOutputO0,
    -- solve R1CS and return output with logs
    solveOutputAndCollectLogWithOpts,
    -- helper functions
    elaborateAndEncode,
    asGF181N,
  )
where

import Control.Arrow (left)
import Control.Monad ((>=>))
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.Semiring (Semiring (one, zero))
import Data.Vector (Vector)
import Keelung (Encode, N (..))
import Keelung qualified as Lang
import Keelung.Compiler.Compile qualified as Compile
import Keelung.Compiler.ConstraintModule (ConstraintModule)
import Keelung.Compiler.ConstraintSystem (ConstraintSystem (..))
import Keelung.Compiler.Error
import Keelung.Compiler.Linker qualified as Linker
import Keelung.Compiler.Optimize qualified as Optimizer
import Keelung.Compiler.Optimize.ConstantPropagation qualified as ConstantPropagation
import Keelung.Compiler.Options
import Keelung.Compiler.R1CS
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Compiler.Syntax.Internal (Internal (..))
import Keelung.Compiler.Syntax.ToInternal as ToInternal
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Data.FieldInfo
import Keelung.Field (GF181)
import Keelung.Interpreter qualified as Interpreter
import Keelung.Monad (Comp)
import Keelung.Solver qualified as Solver
import Keelung.Syntax.Counters
import Keelung.Syntax.Encode.Syntax (Elaborated)
import Keelung.Syntax.Encode.Syntax qualified as Encoded

--------------------------------------------------------------------------------
-- Interpreters

-- Interprets a Keelung program with given inputs
interpret :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> Either (Error n) [Integer]
interpret fieldInfo prog rawPublicInputs rawPrivateInputs = do
  elab <- elaborateAndEncode prog
  let counters = Encoded.compCounters (Encoded.elabComp elab)
  inputs <- left InputError (Inputs.deserialize counters rawPublicInputs rawPrivateInputs)
  map toInteger <$> left InterpreterError (Interpreter.run fieldInfo elab inputs)

-- | Interpret an elaborated program with given inputs
interpretElab :: (GaloisField n, Integral n) => FieldInfo -> Elaborated -> [Integer] -> [Integer] -> Either (Error n) [Integer]
interpretElab fieldInfo elab rawPublicInputs rawPrivateInputs = do
  let counters = Encoded.compCounters (Encoded.elabComp elab)
  inputs <- left InputError (Inputs.deserialize counters rawPublicInputs rawPrivateInputs)
  left InterpreterError (Interpreter.run fieldInfo elab inputs)

--------------------------------------------------------------------------------
-- Witness generation / R1CS solving

-- | Given a Keelung program and a list of raw public inputs and private inputs,
--   Generate (structured inputs, outputs, witness)
generateWitness :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> Either (Error n) (Counters, Vector n, Vector n)
generateWitness fieldInfo program rawPublicInputs rawPrivateInputs = do
  elab <- elaborateAndEncode program
  generateWitnessElab fieldInfo elab rawPublicInputs rawPrivateInputs

generateWitnessElab :: (GaloisField n, Integral n) => FieldInfo -> Elaborated -> [Integer] -> [Integer] -> Either (Error n) (Counters, Vector n, Vector n)
generateWitnessElab fieldInfo elab rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS . Linker.linkConstraintModule <$> compileO1Elab fieldInfo elab
  let counters = r1csCounters r1cs
  inputs <- left InputError (Inputs.deserialize counters rawPublicInputs rawPrivateInputs)
  (outputs, witness) <- left SolverError (Solver.run defaultOptions r1cs inputs)
  return (counters, outputs, witness)

-- | R1CS witness solver
solveOutputElabWithOpts :: (GaloisField n, Integral n) => Options -> Elaborated -> [Integer] -> [Integer] -> Either (Error n) [Integer]
solveOutputElabWithOpts options elab rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS . Linker.linkConstraintModule <$> compileElabWithOpts options elab
  inputs <- left InputError (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case Solver.run options r1cs inputs of
    Left err -> Left (SolverError err)
    Right (outputs, _) -> Right (toList $ Inputs.deserializeBinReps (r1csCounters r1cs) outputs)

solveOutputWithOpts :: (GaloisField n, Integral n, Encode t) => Options -> Comp t -> [Integer] -> [Integer] -> Either (Error n) [Integer]
solveOutputWithOpts options prog rawPublicInputs rawPrivateInputs = do
  elab <- elaborateAndEncode prog
  solveOutputElabWithOpts options elab rawPublicInputs rawPrivateInputs

solveOutput :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> Either (Error n) [Integer]
solveOutput fieldInfo = solveOutputWithOpts (defaultOptions {optFieldInfo = fieldInfo})

-- | R1CS witness solver (on unoptimized R1CS)
solveOutputO0 :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> Either (Error n) [Integer]
solveOutputO0 fieldInfo = solveOutputWithOpts (defaultOptions {optFieldInfo = fieldInfo, optOptimize = False})

-- | Generate R1CS witness solver report (on optimized R1CS)
solveOutputAndCollectLogWithOpts :: (GaloisField n, Integral n, Encode t) => Options -> Comp t -> [Integer] -> [Integer] -> (Maybe (Error n), Maybe (Solver.LogReport n))
solveOutputAndCollectLogWithOpts options prog rawPublicInputs rawPrivateInputs = case do
  r1cs <- toR1CS <$> compileAndLinkWithOpts options prog
  inputs <- left InputError (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  return (r1cs, inputs) of
  Left err -> (Just err, Nothing)
  Right (r1cs, inputs) -> case Solver.debug r1cs inputs of
    (Left err, logs) -> (Just (SolverError err), logs)
    (Right _, logs) -> (Nothing, logs)

--------------------------------------------------------------------------------
-- Compilation

-- | Compile an Internal syntax to a constraint module with options
compileInternalWithOpts :: (GaloisField n, Integral n) => Options -> Internal n -> Either (Error n) (ConstraintModule n)
compileInternalWithOpts options =
  let constProp = optConstProp options
      optimize = optOptimize options
   in ( Compile.run options -- compile
          . (if constProp then ConstantPropagation.run else id) -- constant propagation
          >=> (if optimize then left CompilerError . Optimizer.run else Right) -- optimize
      )

-- | Compile an elaborated program to a constraint module with options
compileElabWithOpts :: (GaloisField n, Integral n) => Options -> Elaborated -> Either (Error n) (ConstraintModule n)
compileElabWithOpts options = compileInternalWithOpts options . ToInternal.run (optFieldInfo options)

-- | Compile a Keelung program to a constraint module with options
compileWithOpts :: (GaloisField n, Integral n, Encode t) => Options -> Comp t -> Either (Error n) (ConstraintModule n)
compileWithOpts options = elaborateAndEncode >=> compileElabWithOpts options

-- | Compile a Keelung program to a constraint system with options
compileAndLinkWithOpts :: (GaloisField n, Integral n, Encode t) => Options -> Comp t -> Either (Error n) (ConstraintSystem n)
compileAndLinkWithOpts options program = Linker.linkConstraintModule <$> compileWithOpts options program

-- | Compile a Keelung program to a constraint system with optimization turned on
compileAndLink ::
  (GaloisField n, Integral n, Encode t) =>
  FieldInfo ->
  Comp t ->
  Either (Error n) (ConstraintSystem n)
compileAndLink fieldInfo = compileAndLinkWithOpts (defaultOptions {optFieldInfo = fieldInfo, optOptimize = True})

-- | `compileElabWithOpt` with optimization turned off
compileO0Elab :: (GaloisField n, Integral n) => FieldInfo -> Elaborated -> Either (Error n) (ConstraintModule n)
compileO0Elab fieldInfo = compileElabWithOpts (defaultOptions {optFieldInfo = fieldInfo, optConstProp = True, optOptimize = False})

-- | `compileElabWithOpt` with optimization turned on
compileO1Elab :: (GaloisField n, Integral n) => FieldInfo -> Elaborated -> Either (Error n) (ConstraintModule n)
compileO1Elab fieldInfo = compileElabWithOpts (defaultOptions {optFieldInfo = fieldInfo, optConstProp = True, optOptimize = True})

--------------------------------------------------------------------------------

-- | Elaborates a Keelung program
elaborateAndEncode :: (Encode t) => Comp t -> Either (Error n) Elaborated
elaborateAndEncode = left LangError . Lang.elaborateAndEncode

-- | Helper function for fixing the type as `N GF181`
asGF181N :: Either (Error (N GF181)) a -> Either (Error (N GF181)) a
asGF181N = id