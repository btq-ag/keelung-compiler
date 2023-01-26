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
    elaborate,
    interpret,
    genInputsOutputsWitnesses,
    compileOnly,
    compile,
    compileO0,
    compileO1,
    compileO1',
    compileO2,
    optimizeWithInput,
    --
    compileO0Elab,
    compileO1Elab,
    compileO2Elab,
    interpretElab,
    genInputsOutputsWitnessesElab,
    --
    asGF181N,
    asGF181,
  )
where

import Control.Arrow (left)
import Data.Field.Galois (GaloisField)
import Data.Semiring (Semiring (one, zero))
import Keelung (Encode, N (..))
import qualified Keelung as Lang
import qualified Keelung.Compiler.Compile as Compile
import Keelung.Compiler.Constraint (ConstraintSystem, relocateConstraintSystem)
import Keelung.Compiler.Error
import qualified Keelung.Compiler.Optimize as Optimizer
import qualified Keelung.Compiler.Optimize.ConstantPropagation as ConstantPropagation
import Keelung.Compiler.R1CS
import Keelung.Compiler.Relocated (RelocatedConstraintSystem (..), numberOfConstraints)
import Keelung.Compiler.Syntax.Erase as Erase
import Keelung.Compiler.Syntax.Inputs (Inputs)
import qualified Keelung.Compiler.Syntax.Inputs as Inputs
import Keelung.Compiler.Syntax.Untyped (TypeErased (..))
import Keelung.Compiler.Util (Witness)
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Field (GF181)
import qualified Keelung.Interpreter.Typed as Typed
import Keelung.Monad (Comp)
import Keelung.Syntax.Typed (Elaborated)

--------------------------------------------------------------------------------
-- Top-level functions that accepts Keelung programs

elaborate :: Encode t => Comp t -> Either (Error n) Elaborated
elaborate = left LangError . Lang.elaborate

-- elaboration => interpretation
interpret :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) [n]
interpret prog rawInputs = do
  elab <- elaborate prog
  let inputs = Inputs.deserializeElab elab rawInputs
  left InterpretError (Typed.run elab inputs)

-- | Given a Keelung program and a list of raw inputs
--   Generate (structured inputs, outputs, witness)
genInputsOutputsWitnesses :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) (Inputs n, [n], Witness n)
genInputsOutputsWitnesses prog rawInputs = do
  elab <- elaborate prog
  outputs <- left InterpretError (Typed.run elab (Inputs.deserializeElab elab rawInputs))
  r1cs <- toR1CS <$> compileO1 prog
  let inputs = Inputs.deserialize (r1csCounters r1cs) rawInputs
  witness <- left ExecError (witnessOfR1CS inputs r1cs)
  return (inputs, outputs, witness)

-- elaborate => rewrite => type erase
erase :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (TypeErased n)
erase prog = eraseElab <$> elaborate prog

-- elaborate => rewrite => type erase => compile => relocate
compileOnly :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (RelocatedConstraintSystem n)
compileOnly prog = erase prog >>= return . relocateConstraintSystem . Compile.run

-- elaborate => rewrite => type erase => constant propagation => compile => relocate
compileO0 :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (RelocatedConstraintSystem n)
compileO0 prog = erase prog >>= return . relocateConstraintSystem . Compile.run . ConstantPropagation.run

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
compileO1' prog = erase prog >>= return . Optimizer.optimize1' . Compile.run . ConstantPropagation.run

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

interpretElab :: (GaloisField n, Integral n) => Elaborated -> [n] -> Either String [n]
interpretElab elab rawInputs =
  let inputs = Inputs.deserializeElab elab rawInputs
   in left (show . InterpretError) (Typed.run elab inputs)

genInputsOutputsWitnessesElab :: (GaloisField n, Integral n) => Elaborated -> [n] -> Either String (Inputs n, [n], Witness n)
genInputsOutputsWitnessesElab elab rawInputs = do
  outputs <- left (show . InterpretError) (Typed.run elab (Inputs.deserializeElab elab rawInputs))
  r1cs <- toR1CS <$> left show (compileO1Elab elab)
  let inputs = Inputs.deserialize (r1csCounters r1cs) rawInputs
  witness <- left (show . ExecError) (witnessOfR1CS inputs r1cs)
  return (inputs, outputs, witness)

compileO0Elab :: (GaloisField n, Integral n) => Elaborated -> Either (Error n) (RelocatedConstraintSystem n)
compileO0Elab = return . relocateConstraintSystem . Compile.run . ConstantPropagation.run . Erase.run

compileO1Elab :: (GaloisField n, Integral n) => Elaborated -> Either (Error n) (RelocatedConstraintSystem n)
compileO1Elab = return . Optimizer.optimize1 . relocateConstraintSystem . Compile.run . ConstantPropagation.run . Erase.run

compileO2Elab :: (GaloisField n, Integral n) => Elaborated -> Either (Error n) (RelocatedConstraintSystem n)
compileO2Elab = return . Optimizer.optimize2 . Optimizer.optimize1 . relocateConstraintSystem . Compile.run . ConstantPropagation.run . Erase.run

--------------------------------------------------------------------------------

asGF181N :: Either (Error (N GF181)) a -> Either (Error (N GF181)) a
asGF181N = id

asGF181 :: Either (Error GF181) a -> Either (Error GF181) a
asGF181 = id