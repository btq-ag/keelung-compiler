-- | Top level functions for everything?
module Keelung.Compiler
  ( module Keelung.Compiler.Error,
    GaloisField,
    Semiring (one, zero),
    module Prelude,
    ConstraintSystem (..),
    Internal (..),
    R1CS (..),
    -- interpret
    interpret,
    interpretE,
    -- compile to ConstraintModule
    compile,
    compileWithOpts,
    compileWithOptsE,
    compileWithOptsI,
    -- generate witness
    generateWitness,
    generateWitnessWithOpts,
    generateWitnessWithOptsE,
    generateWitnessWithOptsI,
    -- solve R1CS and return output
    solve,
    solveWithOpts,
    solveWithOptsE,
    solveWithOptsI,
    -- solve R1CS and return output with logs
    solveAndCollectLog,
    solveAndCollectLogWithOpts,
    solveAndCollectLogWithOptsI,
    -- helper functions
    deserializeInputs,
    elaborateAndEncode,
    toInternalWithOpts,
    link,
    toR1CS,
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
import Keelung.Compiler.Options qualified as Options
import Keelung.Compiler.R1CS qualified as R1CS
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Compiler.Syntax.Internal (Internal (..))
import Keelung.Compiler.Syntax.ToInternal as ToInternal
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Data.FieldInfo
import Keelung.Field (FieldType, GF181)
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
  inputs <- deserializeInputs counters rawPublicInputs rawPrivateInputs
  map toInteger <$> left InterpreterError (Interpreter.run fieldInfo elab inputs)

-- | Interpret an elaborated program with given inputs
interpretE :: (GaloisField n, Integral n) => FieldInfo -> Elaborated -> [Integer] -> [Integer] -> Either (Error n) [Integer]
interpretE fieldInfo elab rawPublicInputs rawPrivateInputs = do
  let counters = Encoded.compCounters (Encoded.elabComp elab)
  inputs <- deserializeInputs counters rawPublicInputs rawPrivateInputs
  left InterpreterError (Interpreter.run fieldInfo elab inputs)

--------------------------------------------------------------------------------
-- Witness generation / R1CS solving

-- | Given an Internal syntaxs and a list of raw public inputs and private inputs,
--   Generate (structured inputs, outputs, witness)
generateWitnessWithOptsI :: (GaloisField n, Integral n) => Options -> Internal n -> [Integer] -> [Integer] -> Either (Error n) (Counters, Vector n, Vector n)
generateWitnessWithOptsI options syntax rawPublicInputs rawPrivateInputs = do
  r1cs <- compileWithOptsI options syntax >>= link >>= toR1CS
  let counters = r1csCounters r1cs
  inputs <- deserializeInputs counters rawPublicInputs rawPrivateInputs
  (outputs, witness) <- left SolverError (Solver.run defaultOptions r1cs inputs)
  return (counters, outputs, witness)

-- | Given an Elaborated syntax and a list of raw public inputs and private inputs,
--   Generate (structured inputs, outputs, witness)
generateWitnessWithOptsE :: (GaloisField n, Integral n) => Options -> Elaborated -> [Integer] -> [Integer] -> Either (Error n) (Counters, Vector n, Vector n)
generateWitnessWithOptsE options elab rawPublicInputs rawPrivateInputs = toInternalWithOpts options elab >>= \syntax -> generateWitnessWithOptsI options syntax rawPublicInputs rawPrivateInputs

-- | Given a Keelung program and a list of raw public inputs and private inputs,
--   Generate (structured inputs, outputs, witness)
generateWitnessWithOpts :: (GaloisField n, Integral n, Encode t) => Options -> Comp t -> [Integer] -> [Integer] -> Either (Error n) (Counters, Vector n, Vector n)
generateWitnessWithOpts options program rawPublicInputs rawPrivateInputs = elaborateAndEncode program >>= \elab -> generateWitnessWithOptsE options elab rawPublicInputs rawPrivateInputs

-- | `generateWitnessWithOpts` with default options
generateWitness :: (GaloisField n, Integral n, Encode t) => FieldType -> Comp t -> [Integer] -> [Integer] -> Either (Error n) (Counters, Vector n, Vector n)
generateWitness = generateWitnessWithOpts . Options.new

--------------------------------------------------------------------------------
-- R1CS solving

-- | Solve R1CS with inputs and generate outputs (takes Internal syntax)
solveWithOptsI :: (GaloisField n, Integral n) => Options -> Internal n -> [Integer] -> [Integer] -> Either (Error n) [Integer]
solveWithOptsI options syntax rawPublicInputs rawPrivateInputs = do
  (counters, outputs, _) <- generateWitnessWithOptsI options syntax rawPublicInputs rawPrivateInputs
  Right (toList $ Inputs.deserializeBinReps counters outputs)

-- | Solve R1CS with inputs and generate outputs (takes Elaborated syntax)
solveWithOptsE :: (GaloisField n, Integral n) => Options -> Elaborated -> [Integer] -> [Integer] -> Either (Error n) [Integer]
solveWithOptsE options elab rawPublicInputs rawPrivateInputs = toInternalWithOpts options elab >>= \syntax -> solveWithOptsI options syntax rawPublicInputs rawPrivateInputs

-- | Solve R1CS with inputs and generate outputs (takes Keelung program)
solveWithOpts :: (GaloisField n, Integral n, Encode t) => Options -> Comp t -> [Integer] -> [Integer] -> Either (Error n) [Integer]
solveWithOpts options prog rawPublicInputs rawPrivateInputs = do
  elab <- elaborateAndEncode prog
  solveWithOptsE options elab rawPublicInputs rawPrivateInputs

-- | `solveWithOpts` with default options
solve :: (GaloisField n, Integral n, Encode t) => Lang.FieldType -> Comp t -> [Integer] -> [Integer] -> Either (Error n) [Integer]
solve = solveWithOpts . Options.new

-- | Solve R1CS with inputs and generate outputs + logs (takes Internal syntax)
solveAndCollectLogWithOptsI :: (GaloisField n, Integral n) => Options -> Internal n -> [Integer] -> [Integer] -> (Maybe (Error n), Maybe (Solver.LogReport n))
solveAndCollectLogWithOptsI options syntax rawPublicInputs rawPrivateInputs = case do
  r1cs <- compileWithOptsI options syntax >>= link >>= toR1CS
  inputs <- deserializeInputs (r1csCounters r1cs) rawPublicInputs rawPrivateInputs
  return (r1cs, inputs) of
  Left err -> (Just err, Nothing)
  Right (r1cs, inputs) -> case Solver.debug r1cs inputs of
    (Left err, logs) -> (Just (SolverError err), logs)
    (Right _, logs) -> (Nothing, logs)

-- | Solve R1CS with inputs and generate outputs + logs (takes Keepung program)
solveAndCollectLogWithOpts :: (GaloisField n, Integral n, Encode t) => Options -> Comp t -> [Integer] -> [Integer] -> (Maybe (Error n), Maybe (Solver.LogReport n))
solveAndCollectLogWithOpts options prog rawPublicInputs rawPrivateInputs = case do
  r1cs <- compileWithOpts options prog >>= link >>= toR1CS
  inputs <- deserializeInputs (r1csCounters r1cs) rawPublicInputs rawPrivateInputs
  return (r1cs, inputs) of
  Left err -> (Just err, Nothing)
  Right (r1cs, inputs) -> case Solver.debug r1cs inputs of
    (Left err, logs) -> (Just (SolverError err), logs)
    (Right _, logs) -> (Nothing, logs)

-- | `solveAndCollectLog` with default options
solveAndCollectLog :: (GaloisField n, Integral n, Encode t) => FieldType -> Comp t -> [Integer] -> [Integer] -> (Maybe (Error n), Maybe (Solver.LogReport n))
solveAndCollectLog = solveAndCollectLogWithOpts . Options.new

--------------------------------------------------------------------------------
-- Compilation

-- | Compile an Internal syntax to a constraint module with options
compileWithOptsI :: (GaloisField n, Integral n) => Options -> Internal n -> Either (Error n) (ConstraintModule n)
compileWithOptsI options =
  let constProp = optConstProp options
      optimize = optOptimize options
   in ( Compile.run options -- compile
          . (if constProp then ConstantPropagation.run else id) -- constant propagation
          >=> (if optimize then left CompilerError . Optimizer.run else Right) -- optimize
      )

-- | Compile an elaborated program to a constraint module with options
compileWithOptsE :: (GaloisField n, Integral n) => Options -> Elaborated -> Either (Error n) (ConstraintModule n)
compileWithOptsE options = toInternalWithOpts options >=> compileWithOptsI options

-- | Compile a Keelung program to a constraint module with options
compileWithOpts :: (GaloisField n, Integral n, Encode t) => Options -> Comp t -> Either (Error n) (ConstraintModule n)
compileWithOpts options = elaborateAndEncode >=> compileWithOptsE options

-- | Compile a Keelung program to a constraint module with default options
compile :: (GaloisField n, Integral n, Encode t) => FieldType -> Comp t -> Either (Error n) (ConstraintModule n)
compile = compileWithOpts . Options.new

--------------------------------------------------------------------------------

-- | Keelung Program -> Elaborated Syntax
elaborateAndEncode :: (Encode t) => Comp t -> Either (Error n) Elaborated
elaborateAndEncode = left LangError . Lang.elaborateAndEncode

-- | Elaborated Syntax -> Internal Syntax
toInternalWithOpts :: (GaloisField n, Integral n) => Options -> Elaborated -> Either (Error n) (Internal n)
toInternalWithOpts options = Right . ToInternal.run (optFieldInfo options)

-- | ConstraintModule -> ConstraintSystem
link :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Error n) (ConstraintSystem n)
link = Right . Linker.linkConstraintModule

-- | ConstraintSystem -> R1CS
toR1CS :: (GaloisField n) => ConstraintSystem n -> Either (Error n) (R1CS n)
toR1CS = Right . R1CS.fromConstraintSystem

-- | Deserialize raw inputs into structured inputs
deserializeInputs :: (GaloisField n, Integral n) => Counters -> [Integer] -> [Integer] -> Either (Error n) (Inputs.Inputs n)
deserializeInputs counters rawPublicInputs rawPrivateInputs = left InputError (Inputs.deserialize counters rawPublicInputs rawPrivateInputs)

-- | Helper function for fixing the type as `N GF181`
asGF181N :: Either (Error (N GF181)) a -> Either (Error (N GF181)) a
asGF181N = id