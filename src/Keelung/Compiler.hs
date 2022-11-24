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
    compileO2,
    optimizeWithInput,
    -- computeWitness,
    execute,
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
import Control.Monad (when)
import Data.Field.Galois (GaloisField)
import Data.Semiring (Semiring (one, zero))
import Keelung (Encode, N (..))
import qualified Keelung as Lang
import qualified Keelung.Compiler.Compile as Compile
import Keelung.Compiler.Constraint (ConstraintSystem (..), numberOfConstraints)
import Keelung.Compiler.Error
import qualified Keelung.Compiler.Interpret as Interpret
import qualified Keelung.Compiler.Interpret.R1CS as Interpret.R1CS
import qualified Keelung.Compiler.Optimize as Optimizer
import qualified Keelung.Compiler.Optimize.ConstantPropagation as ConstantPropagation
import qualified Keelung.Compiler.Optimize.Rewriting as Rewriting
import Keelung.Compiler.R1CS
import Keelung.Compiler.Syntax.Erase as Erase
import Keelung.Compiler.Syntax.Inputs (Inputs)
import qualified Keelung.Compiler.Syntax.Inputs as Inputs
import Keelung.Compiler.Syntax.Untyped (TypeErased (..))
import Keelung.Compiler.Util (Witness)
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Field (GF181)
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
  left InterpretError (Interpret.run elab inputs)

-- | Given a Keelung program and a list of raw inputs
--   Generate (structured inputs, outputs, witness)
genInputsOutputsWitnesses :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) (Inputs n, [n], Witness n)
genInputsOutputsWitnesses prog rawInputs = do
  elab <- elaborate prog
  outputs <- left InterpretError (Interpret.run elab (Inputs.deserializeElab elab rawInputs))
  r1cs <- toR1CS <$> compileO1 prog
  let inputs = Inputs.deserialize (r1csVarCounters r1cs) rawInputs
  witness <- left ExecError (witnessOfR1CS inputs r1cs)
  return (inputs, outputs, witness)

-- elaboration => rewriting => type erasure
erase :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (TypeErased n)
erase prog = elaborate prog >>= eraseElab

-- elaboration => rewriting => type erasure => compilation
compileOnly :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (ConstraintSystem n)
compileOnly prog = erase prog >>= return . Compile.run

-- | elaboration => rewriting => type erasure => constant propagation => compilation
compileO0 :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (ConstraintSystem n)
compileO0 prog = erase prog >>= return . Compile.run . ConstantPropagation.run

-- | elaboration => rewriting => type erasure => constant propagation => compilation => optimisation I
compileO1 ::
  (GaloisField n, Integral n, Encode t) =>
  Comp t ->
  Either (Error n) (ConstraintSystem n)
compileO1 prog = compileO0 prog >>= return . Optimizer.optimize1

-- | 'compile' defaults to 'compileO1'
compile ::
  (GaloisField n, Integral n, Encode t) =>
  Comp t ->
  Either (Error n) (ConstraintSystem n)
compile = compileO1

-- | elaboration => rewriting => type erasure => constant propagation => compilation => optimisation I + II
compileO2 ::
  (GaloisField n, Integral n, Encode t) =>
  Comp t ->
  Either (Error n) (ConstraintSystem n)
compileO2 prog = compileO1 prog >>= return . Optimizer.optimize2

-- with optimisation + partial evaluation with inputs
optimizeWithInput ::
  (GaloisField n, Integral n, Encode t) =>
  Comp t ->
  [n] ->
  Either (Error n) (ConstraintSystem n)
optimizeWithInput program inputs = do
  cs <- compile program
  let (_, cs') = Optimizer.optimizeWithInput inputs cs
  return cs'

-- computes witnesses
-- computeWitness :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) (Witness n)
-- computeWitness prog inputs = compile prog >>= left ExecError . witnessOfR1CS inputs . toR1CS

-- | (1) Compile to R1CS.
--   (2) Generate a satisfying assignment, 'w'.
--   (3) Check whether 'w' satisfies the constraint system produced in (1).
--   (4) Check whether the R1CS result matches the interpreter result.
execute :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) [n]
execute prog rawInputs = do
  elab <- elaborate prog

  r1cs <- toR1CS <$> compile prog
  let inputs = Inputs.deserialize (r1csVarCounters r1cs) rawInputs
  (actualOutputs, actualWitness) <- left ExecError (Interpret.R1CS.run' r1cs inputs)

  -- interpret the program to see if the output value is correct
  expectedOutputs <- left InterpretError (Interpret.run elab inputs)

  when (actualOutputs /= expectedOutputs) $ do
    Left $ ExecError $ ExecOutputError expectedOutputs actualOutputs

  case satisfyR1CS actualWitness r1cs of
    Nothing -> return ()
    Just r1c's ->
      Left $
        ExecError $
          ExecR1CUnsatisfiableError r1c's actualWitness

  return actualOutputs

--------------------------------------------------------------------------------
-- Top-level functions that accepts elaborated programs

eraseElab :: (GaloisField n, Integral n) => Elaborated -> Either (Error n) (TypeErased n)
eraseElab elab = left LangError (Rewriting.run elab) >>= return . Erase.run

interpretElab :: (GaloisField n, Integral n) => Elaborated -> [n] -> Either String [n]
interpretElab elab rawInputs =
  let inputs = Inputs.deserializeElab elab rawInputs
   in left (show . InterpretError) (Interpret.run elab inputs)

genInputsOutputsWitnessesElab :: (GaloisField n, Integral n) => Elaborated -> [n] -> Either String (Inputs n, [n], Witness n)
genInputsOutputsWitnessesElab elab rawInputs = do
  outputs <- left (show . InterpretError) (Interpret.run elab (Inputs.deserializeElab elab rawInputs))
  r1cs <- toR1CS <$> left show (compileO1Elab elab)
  let inputs = Inputs.deserialize (r1csVarCounters r1cs) rawInputs
  witness <- left (show . ExecError) (witnessOfR1CS inputs r1cs)
  return (inputs, outputs, witness)

compileO0Elab :: (GaloisField n, Integral n) => Elaborated -> Either (Error n) (ConstraintSystem n)
compileO0Elab elab = do
  rewritten <- left LangError (Rewriting.run elab)
  return $ Compile.run $ ConstantPropagation.run $ Erase.run rewritten

compileO1Elab :: (GaloisField n, Integral n) => Elaborated -> Either (Error n) (ConstraintSystem n)
compileO1Elab elab = do
  rewritten <- left LangError (Rewriting.run elab)
  return $ Optimizer.optimize1 $ Compile.run $ ConstantPropagation.run $ Erase.run rewritten

compileO2Elab :: (GaloisField n, Integral n) => Elaborated -> Either (Error n) (ConstraintSystem n)
compileO2Elab elab = do
  rewritten <- left LangError (Rewriting.run elab)
  return $ Optimizer.optimize2 $ Optimizer.optimize1 $ Compile.run $ ConstantPropagation.run $ Erase.run rewritten

--------------------------------------------------------------------------------

asGF181N :: Either (Error (N GF181)) a -> Either (Error (N GF181)) a
asGF181N = id

asGF181 :: Either (Error GF181) a -> Either (Error GF181) a
asGF181 = id