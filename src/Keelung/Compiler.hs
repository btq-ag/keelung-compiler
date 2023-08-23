{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Compiler
  ( module Keelung.Compiler.Error,
    GaloisField,
    Semiring (one, zero),
    module Prelude,
    ConstraintSystem (..),
    numberOfConstraints,
    Internal (..),
    module Keelung.Compiler.R1CS,
    --
    convertToInternal,
    elaborateAndEncode,
    interpret,
    -- genInputsOutputsWitnesses,
    generateWitness,
    compileWithoutConstProp,
    compile,
    -- compileO0Old,
    compileO0,
    -- compileO1Old,
    compileO1,
    compileToModules,
    -- optimizeWithInput,
    --
    -- compileO0OldElab,
    compileO0Elab,
    -- compileO1OldElab,
    compileO1Elab,
    interpretElab,
    generateWitnessElab,
    --
    asGF181N,
    asGF181,
  )
where

import Control.Arrow (left)
import Control.Monad ((>=>))
import Data.Field.Galois (GaloisField)
import Data.Semiring (Semiring (one, zero))
import Data.Vector (Vector)
import Keelung (Encode, N (..))
import Keelung qualified as Lang
import Keelung.Compiler.Compile qualified as Compile
import Keelung.Compiler.ConstraintModule (ConstraintModule)
import Keelung.Compiler.ConstraintSystem (ConstraintSystem (..), numberOfConstraints)
import Keelung.Compiler.Error
import Keelung.Compiler.Linker qualified as Linker
import Keelung.Compiler.Optimize qualified as Optimizer
import Keelung.Compiler.Optimize.ConstantPropagation qualified as ConstantPropagation
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
-- Top-level functions that accepts Keelung programs

elaborateAndEncode :: Encode t => Comp t -> Either (Error n) Elaborated
elaborateAndEncode = left LangError . Lang.elaborateAndEncode

-- elaboration => interpretation
interpret :: (GaloisField n, Integral n, Encode t) => Comp t -> [Integer] -> [Integer] -> Either (Error n) [Integer]
interpret prog rawPublicInputs rawPrivateInputs = do
  elab <- elaborateAndEncode prog
  let counters = Encoded.compCounters (Encoded.elabComp elab)
  inputs <- left InputError (Inputs.deserialize counters rawPublicInputs rawPrivateInputs)
  map toInteger <$> left InterpreterError (Interpreter.run elab inputs)

-- | Given a Keelung program and a list of raw public inputs and private inputs,
--   Generate (structured inputs, outputs, witness)
generateWitness :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> Either (Error n) (Counters, Vector n, Vector n)
generateWitness fieldInfo program rawPublicInputs rawPrivateInputs = do
  elab <- elaborateAndEncode program
  generateWitnessElab fieldInfo elab rawPublicInputs rawPrivateInputs

-- elaborate => rewrite => to internal syntax
convertToInternal :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> Either (Error n) (Internal n)
convertToInternal fieldInfo prog = ToInternal.run fieldInfo <$> elaborateAndEncode prog

-- elaborate => rewrite => to internal syntax => compile => link
compileWithoutConstProp :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> Either (Error n) (ConstraintSystem n)
compileWithoutConstProp fieldInfo prog = elaborateAndEncode prog >>= compileO0Elab fieldInfo >>= return . Linker.linkConstraintModule

-- elaborate => rewrite => to internal syntax => constant propagation => compile
compileO0 :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> Either (Error n) (ConstraintSystem n)
compileO0 fieldInfo prog = elaborateAndEncode prog >>= compileO0Elab fieldInfo >>= return . Linker.linkConstraintModule

-- elaborate => rewrite => to internal syntax => constant propagation => compile => optimisation (new) => link
compileO1 :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> Either (Error n) (ConstraintSystem n)
compileO1 fieldInfo prog = elaborateAndEncode prog >>= compileO1Elab fieldInfo

-- elaborate => rewrite => to internal syntax => constant propagation => compile => optimisation (new)
compileToModules ::
  (GaloisField n, Integral n, Encode t) =>
  FieldInfo ->
  Comp t ->
  Either (Error n) (ConstraintModule n)
compileToModules fieldInfo prog = elaborateAndEncode prog >>= Compile.run fieldInfo . ConstantPropagation.run . ToInternal.run fieldInfo >>= left CompilerError . Optimizer.run

-- | 'compile' defaults to 'compileO1'
compile ::
  (GaloisField n, Integral n, Encode t) =>
  FieldInfo ->
  Comp t ->
  Either (Error n) (ConstraintSystem n)
compile = compileO1

--------------------------------------------------------------------------------
-- Top-level functions that accepts elaborated programs

interpretElab :: (GaloisField n, Integral n) => Elaborated -> [Integer] -> [Integer] -> Either (Error n) [Integer]
interpretElab elab rawPublicInputs rawPrivateInputs = do
  let counters = Encoded.compCounters (Encoded.elabComp elab)
  inputs <- left InputError (Inputs.deserialize counters rawPublicInputs rawPrivateInputs)
  left InterpreterError (Interpreter.run elab inputs)

generateWitnessElab :: (GaloisField n, Integral n) => FieldInfo -> Elaborated -> [Integer] -> [Integer] -> Either (Error n) (Counters, Vector n, Vector n)
generateWitnessElab fieldInfo elab rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS <$> compileO1Elab fieldInfo elab
  let counters = r1csCounters r1cs
  inputs <- left InputError (Inputs.deserialize counters rawPublicInputs rawPrivateInputs)
  (outputs, witness) <- left SolverError (Solver.run r1cs inputs)
  return (counters, outputs, witness)

compileO0Elab :: (GaloisField n, Integral n) => FieldInfo -> Elaborated -> Either (Error n) (ConstraintModule n)
compileO0Elab fieldInfo = Compile.run fieldInfo . ConstantPropagation.run . ToInternal.run fieldInfo

compileO1Elab :: (GaloisField n, Integral n) => FieldInfo -> Elaborated -> Either (Error n) (ConstraintSystem n)
compileO1Elab fieldInfo = Compile.run fieldInfo . ConstantPropagation.run . ToInternal.run fieldInfo >=> left CompilerError . Optimizer.run >=> return . Linker.linkConstraintModule

--------------------------------------------------------------------------------

asGF181N :: Either (Error (N GF181)) a -> Either (Error (N GF181)) a
asGF181N = id

asGF181 :: Either (Error GF181) a -> Either (Error GF181) a
asGF181 = id