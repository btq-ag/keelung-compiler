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
    RelocatedConstraintSystem (..),
    numberOfConstraints,
    TypeErased (..),
    module Keelung.Compiler.R1CS,
    --
    erase,
    elaborateAndEncode,
    interpret,
    -- genInputsOutputsWitnesses,
    generateWitness,
    compileWithoutConstProp,
    compile,
    compileO0Old,
    compileO0,
    compileO1Old,
    compileO1,
    compileToModules,
    optimizeWithInput,
    --
    compileO0OldElab,
    compileO0Elab,
    compileO1OldElab,
    compileO1Elab,
    interpretElab,
    generateWitnessElab,
    --
    asGF181N,
    asGF181,
  )
where

import Control.Arrow (left)
import Data.Field.Galois (GaloisField)
import Data.Semiring (Semiring (one, zero))
import Data.Vector (Vector)
import Keelung (Encode, N (..))
import Keelung qualified as Lang
import Keelung.Compiler.Compile qualified as Compile
import Keelung.Compiler.ConstraintSystem (ConstraintSystem, relocateConstraintSystem)
import Keelung.Compiler.Error
import Keelung.Compiler.Optimize qualified as Optimizer
import Keelung.Compiler.Optimize.ConstantPropagation qualified as ConstantPropagation
import Keelung.Compiler.R1CS hiding (generateWitness)
import Keelung.Compiler.Relocated (RelocatedConstraintSystem (..), numberOfConstraints)
import Keelung.Compiler.Relocated qualified as Relocated
import Keelung.Compiler.Syntax.Erase as Erase
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Compiler.Syntax.Untyped (TypeErased (..))
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Field (GF181)
import Keelung.Interpreter.Error qualified as Interpreter
import Keelung.Interpreter.R1CS qualified as R1CS
import Keelung.Interpreter.SyntaxTree qualified as SyntaxTree
import Keelung.Monad (Comp)
import Keelung.Syntax.Counters
import Keelung.Syntax.Encode.Syntax (Elaborated)
import Keelung.Syntax.Encode.Syntax qualified as Encoded

--------------------------------------------------------------------------------
-- Top-level functions that accepts Keelung programs

elaborateAndEncode :: Encode t => Comp t -> Either (Error n) Elaborated
elaborateAndEncode = left LangError . Lang.elaborateAndEncode

-- elaboration => interpretation
interpret :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> Either (Error n) [n]
interpret prog rawPublicInputs rawPrivateInputs = do
  elab <- elaborateAndEncode prog
  let counters = Encoded.compCounters (Encoded.elabComp elab)
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize counters rawPublicInputs rawPrivateInputs)
  left (InterpretError . Interpreter.SyntaxTreeError) (SyntaxTree.run elab inputs)

-- | Given a Keelung program and a list of raw public inputs and private inputs,
--   Generate (structured inputs, outputs, witness)
generateWitness :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> Either (Error n) (Counters, [n], Vector n)
generateWitness program rawPublicInputs rawPrivateInputs = do
  elab <- elaborateAndEncode program
  generateWitnessElab elab rawPublicInputs rawPrivateInputs

-- elaborate => rewrite => type erase
erase :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (TypeErased n)
erase prog = Erase.run <$> elaborateAndEncode prog

-- elaborate => rewrite => type erase => compile => relocate
compileWithoutConstProp :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (RelocatedConstraintSystem n)
compileWithoutConstProp prog = elaborateAndEncode prog >>= compileO0OldElab >>= return . relocateConstraintSystem

-- elaborate => rewrite => type erase => constant propagation => compile => relocate
compileO0Old :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (ConstraintSystem n)
compileO0Old prog = elaborateAndEncode prog >>= compileO0OldElab

-- elaborate => rewrite => type erase => constant propagation => compile => relocate
compileO0 :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (ConstraintSystem n)
compileO0 prog = elaborateAndEncode prog >>= compileO0Elab

-- elaborate => rewrite => type erase => constant propagation => compile => relocate => optimisation (old) => renumber
compileO1Old ::
  (GaloisField n, Integral n, Encode t) =>
  Comp t ->
  Either (Error n) (RelocatedConstraintSystem n)
compileO1Old prog = elaborateAndEncode prog >>= compileO1OldElab

-- elaborate => rewrite => type erase => constant propagation => compile => optimisation (new) => relocate => renumber
compileO1 ::
  (GaloisField n, Integral n, Encode t) =>
  Comp t ->
  Either (Error n) (RelocatedConstraintSystem n)
compileO1 prog = elaborateAndEncode prog >>= compileO1Elab

-- elaborate => rewrite => type erase => constant propagation => compile => optimisation (new)
compileToModules ::
  (GaloisField n, Integral n, Encode t) =>
  Comp t ->
  Either (Error n) (ConstraintSystem n)
compileToModules prog = elaborateAndEncode prog >>= return . Optimizer.optimizeNew . Compile.run True . ConstantPropagation.run . Erase.run

-- | 'compile' defaults to 'compileO1'
compile ::
  (GaloisField n, Integral n, Encode t) =>
  Comp t ->
  Either (Error n) (RelocatedConstraintSystem n)
compile = compileO1

-- with optimisation + partial evaluation with inputs
optimizeWithInput ::
  (GaloisField n, Integral n, Encode t) =>
  Comp t ->
  [n] ->
  Either (Error n) (RelocatedConstraintSystem n)
optimizeWithInput program inputs = do
  cs <- compile program
  let (_, cs') = Optimizer.optimizeWithInput inputs cs
  return cs'

--------------------------------------------------------------------------------
-- Top-level functions that accepts elaborated programs

interpretElab :: (GaloisField n, Integral n) => Elaborated -> [n] -> [n] -> Either (Error n) [n]
interpretElab elab rawPublicInputs rawPrivateInputs = do
  let counters = Encoded.compCounters (Encoded.elabComp elab)
  inputs <- left(InterpretError . Interpreter.InputError) (Inputs.deserialize counters rawPublicInputs rawPrivateInputs)
  left (InterpretError . Interpreter.SyntaxTreeError) (SyntaxTree.run elab inputs)

generateWitnessElab :: (GaloisField n, Integral n) => Elaborated -> [n] -> [n] -> Either (Error n) (Counters, [n], Vector n)
generateWitnessElab elab rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS <$> compileO1OldElab elab
  let counters = r1csCounters r1cs
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize counters rawPublicInputs rawPrivateInputs)
  (outputs, witness) <- left (InterpretError . Interpreter.R1CSError) (R1CS.run' r1cs inputs)
  return (counters, outputs, witness)

compileO0OldElab :: (GaloisField n, Integral n) => Elaborated -> Either (Error n) (ConstraintSystem n)
compileO0OldElab = return . Compile.run False . ConstantPropagation.run . Erase.run

compileO0Elab :: (GaloisField n, Integral n) => Elaborated -> Either (Error n) (ConstraintSystem n)
compileO0Elab = return . Compile.run True . ConstantPropagation.run . Erase.run

compileO1OldElab :: (GaloisField n, Integral n) => Elaborated -> Either (Error n) (RelocatedConstraintSystem n)
compileO1OldElab = return . Optimizer.optimizeOld . relocateConstraintSystem . Compile.run False . ConstantPropagation.run . Erase.run

compileO1Elab :: (GaloisField n, Integral n) => Elaborated -> Either (Error n) (RelocatedConstraintSystem n)
compileO1Elab = return . Relocated.renumberConstraints . relocateConstraintSystem . Optimizer.optimizeNew . Compile.run True . ConstantPropagation.run . Erase.run

--------------------------------------------------------------------------------

asGF181N :: Either (Error (N GF181)) a -> Either (Error (N GF181)) a
asGF181N = id

asGF181 :: Either (Error GF181) a -> Either (Error GF181) a
asGF181 = id