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
    eraseType,
    TypeErased (..),
    module Keelung.Compiler.R1CS,
    --
    erase,
    interpret,
    compile,
    optimize1,
    optimize2,
    optimize3,
    optimizeWithInput,
    computeWitness,
    execute,
    --
    optimizeElab,
    interpElab,
  )
where

import Control.Arrow (left)
import Control.Monad (unless, when)
import qualified Data.Either as Either
import Data.Field.Galois (GaloisField)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Semiring (Semiring (one, zero))
import Keelung (elaborate)
import qualified Keelung.Compiler.Compile as Compile
import Keelung.Compiler.Constraint (ConstraintSystem (..), numberOfConstraints)
import Keelung.Compiler.Error
import qualified Keelung.Compiler.Interpret as Interpret
-- import Keelung.Compiler.Optimize hiding (optimize)
import qualified Keelung.Compiler.Optimize as Optimizer
import qualified Keelung.Compiler.Optimize.ConstantPropagation as ConstantPropagation
import qualified Keelung.Compiler.Optimize.Rewriting as Rewriting
import Keelung.Compiler.R1CS
import Keelung.Compiler.Syntax.Untyped
import Keelung.Compiler.Util (Witness)
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Monad (Comp)
import Keelung.Syntax (Val)
import Keelung.Syntax.Typed (Elaborated)

--------------------------------------------------------------------------------
-- Top-level functions that accepts Keelung programs

-- elaboration => interpretation
interpret :: (GaloisField n, Integral n) => Comp (Val t) -> [n] -> Either (Error n) [n]
interpret prog ins = do
  elab <- left ElabError (elaborate prog)
  left InterpretError (Interpret.run elab ins)

-- elaboration => rewriting => type erasure
erase :: (GaloisField n, Integral n) => Comp (Val t) -> Either (Error n) (TypeErased n)
erase prog = left ElabError (elaborate prog) >>= eraseElab

-- elaboration => rewriting => type erasure => compilation
compile :: (GaloisField n, Integral n) => Comp (Val t) -> Either (Error n) (ConstraintSystem n)
compile prog = erase prog >>= return . Compile.run

-- elaboration => rewriting => type erasure => constant propagation => compilation
optimize1 :: (GaloisField n, Integral n) => Comp (Val t) -> Either (Error n) (ConstraintSystem n)
optimize1 prog = erase prog >>= return . Compile.run . ConstantPropagation.run

-- elaboration => rewriting => type erasure => constant propagation => compilation => optimisation I
optimize2 ::
  (GaloisField n, Integral n) =>
  Comp (Val t) ->
  Either (Error n) (ConstraintSystem n)
optimize2 prog = optimize1 prog >>= return . Optimizer.optimize

-- elaboration => rewriting => type erasure => constant propagation => compilation => optimisation I + II
optimize3 ::
  (GaloisField n, Integral n) =>
  Comp (Val t) ->
  Either (Error n) (ConstraintSystem n)
optimize3 prog = compile prog >>= return . Optimizer.optimize2 . Optimizer.optimize

-- with optimisation + partial evaluation with inputs
optimizeWithInput ::
  (GaloisField n, Integral n) =>
  Comp (Val t) ->
  [n] ->
  Either (Error n) (ConstraintSystem n)
optimizeWithInput program ins = do
  cs <- compile program
  let (_, cs') = Optimizer.optimizeWithInput ins cs
  return cs'

-- computes witnesses
computeWitness :: (GaloisField n, Integral n) => Comp (Val t) -> [n] -> Either (Error n) (Witness n)
computeWitness prog ins = compile prog >>= left ExecError . witnessOfR1CS ins . toR1CS

-- | (1) Compile to R1CS.
--   (2) Generate a satisfying assignment, 'w'.
--   (3) Check whether 'w' satisfies the constraint system produced in (1).
--   (4) Check whether the R1CS result matches the interpreter result.
execute :: (GaloisField n, Integral n) => Comp (Val t) -> [n] -> Either (Error n) [n]
execute prog ins = do
  r1cs <- toR1CS <$> optimize2 prog

  actualWitness <- left ExecError $ witnessOfR1CS ins r1cs

  -- extract the output value from the witness

  let outputVars = IntSet.toList (r1csOutputVars r1cs)
  let (execErrors, actualOutputs) =
        Either.partitionEithers $
          map
            ( \var ->
                case IntMap.lookup var actualWitness of
                  Nothing -> Left var
                  Just value -> Right value
            )
            outputVars

  unless (null execErrors) $ do
    Left $ ExecError $ ExecOutputVarsNotMappedError outputVars actualWitness

  -- interpret the program to see if the output value is correct
  expectedOutputs <- interpret prog ins

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
eraseElab elab = left ElabError (Rewriting.run elab) >>= return . eraseType

interpElab :: (GaloisField n, Integral n) => Elaborated -> [n] -> Either String [n]
interpElab elab ins = left (show . InterpretError) (Interpret.run elab ins)

optimizeElab :: (GaloisField n, Integral n) => Elaborated -> Either (Error n) (ConstraintSystem n)
optimizeElab elab = do
  rewritten <- left ElabError (Rewriting.run elab)
  return $ Optimizer.optimize $ Compile.run $ ConstantPropagation.run $ eraseType rewritten
