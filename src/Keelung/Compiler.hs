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
    compileOnly,
    compile,
    compileO0,
    compileO0',
    compileO1,
    compileO1',
    compileO2,
    optimizeWithInput,
    --
    compileO0Elab,
    compileO1Elab,
    compileO2Elab,
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
import Keelung.Compiler.Constraint (ConstraintSystem, relocateConstraintSystem)
import Keelung.Compiler.Error
import Keelung.Compiler.Optimize qualified as Optimizer
import Keelung.Compiler.Optimize.ConstantPropagation qualified as ConstantPropagation
import Keelung.Compiler.R1CS hiding (generateWitness)
import Keelung.Compiler.Relocated (RelocatedConstraintSystem (..), numberOfConstraints)
import Keelung.Compiler.Syntax.Erase as Erase
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Compiler.Syntax.Untyped (TypeErased (..))
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Field (GF181)
import Keelung.Interpreter.R1CS qualified as R1CS
import Keelung.Interpreter.Typed qualified as Typed
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
  let inputs = Inputs.deserialize counters rawPublicInputs rawPrivateInputs
  left InterpretError (Typed.run elab inputs)

-- | Given a Keelung program and a list of raw public inputs and private inputs,
--   Generate (structured inputs, outputs, witness)
generateWitness :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> Either (Error n) (Counters, [n], Vector n)
generateWitness program rawPublicInputs rawPrivateInputs = do
  elab <- elaborateAndEncode program
  generateWitnessElab elab rawPublicInputs rawPrivateInputs

-- elaborate => rewrite => type erase
erase :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (TypeErased n)
erase prog = eraseElab <$> elaborateAndEncode prog

-- elaborate => rewrite => type erase => compile => relocate
compileOnly :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (RelocatedConstraintSystem n)
compileOnly prog = erase prog >>= return . relocateConstraintSystem . Compile.run False

-- elaborate => rewrite => type erase => constant propagation => compile => relocate
compileO0 :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (RelocatedConstraintSystem n)
compileO0 prog = erase prog >>= return . relocateConstraintSystem . Compile.run False . ConstantPropagation.run

-- elaborate => rewrite => type erase => constant propagation => compile
compileO0' :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (ConstraintSystem n)
compileO0' prog = erase prog >>= return . Compile.run True . ConstantPropagation.run

-- elaborate => rewrite => type erase => constant propagation => compile => relocate => optimisation I
compileO1 ::
  (GaloisField n, Integral n, Encode t) =>
  Comp t ->
  Either (Error n) (RelocatedConstraintSystem n)
compileO1 prog = compileO0 prog >>= return . Optimizer.optimize1

-- elaborate => rewrite => type erase => constant propagation => compile => optimisation (new)
compileO1' ::
  (GaloisField n, Integral n, Encode t) =>
  Comp t ->
  Either (Error n) (ConstraintSystem n)
compileO1' prog = erase prog >>= return . Optimizer.optimize1' . Compile.run True . ConstantPropagation.run

-- | 'compile' defaults to 'compileO1'
compile ::
  (GaloisField n, Integral n, Encode t) =>
  Comp t ->
  Either (Error n) (RelocatedConstraintSystem n)
compile = compileO1

-- | elaboration => rewriting => type erasure => constant propagation => compilation => optimisation I + II
compileO2 ::
  (GaloisField n, Integral n, Encode t) =>
  Comp t ->
  Either (Error n) (RelocatedConstraintSystem n)
compileO2 prog = compileO1 prog >>= return . Optimizer.optimize2

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

eraseElab :: (GaloisField n, Integral n) => Elaborated -> TypeErased n
eraseElab = Erase.run

interpretElab :: (GaloisField n, Integral n) => Elaborated -> [n] -> [n] -> Either String [n]
interpretElab elab rawPublicInputs rawPrivateInputs =
  let counters = Encoded.compCounters (Encoded.elabComp elab)
      inputs = Inputs.deserialize counters rawPublicInputs rawPrivateInputs
   in left (show . InterpretError) (Typed.run elab inputs)

generateWitnessElab :: (GaloisField n, Integral n) => Elaborated -> [n] -> [n] -> Either (Error n) (Counters, [n], Vector n)
generateWitnessElab elab rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS <$> compileO1Elab elab
  let counters = r1csCounters r1cs
  let inputs = Inputs.deserialize counters rawPublicInputs rawPrivateInputs
  (outputs, witness) <- left InterpretError (R1CS.run' r1cs inputs)
  return (counters, outputs, witness)

compileO0Elab :: (GaloisField n, Integral n) => Elaborated -> Either (Error n) (RelocatedConstraintSystem n)
compileO0Elab = return . relocateConstraintSystem . Compile.run False . ConstantPropagation.run . Erase.run

compileO1Elab :: (GaloisField n, Integral n) => Elaborated -> Either (Error n) (RelocatedConstraintSystem n)
compileO1Elab = return . Optimizer.optimize1 . relocateConstraintSystem . Compile.run False . ConstantPropagation.run . Erase.run

compileO2Elab :: (GaloisField n, Integral n) => Elaborated -> Either (Error n) (RelocatedConstraintSystem n)
compileO2Elab = return . Optimizer.optimize2 . Optimizer.optimize1 . relocateConstraintSystem . Compile.run False . ConstantPropagation.run . Erase.run

--------------------------------------------------------------------------------

asGF181N :: Either (Error (N GF181)) a -> Either (Error (N GF181)) a
asGF181N = id

asGF181 :: Either (Error GF181) a -> Either (Error GF181) a
asGF181 = id