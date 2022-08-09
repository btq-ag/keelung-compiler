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
    module Keelung.Compiler.Optimise,
    erase,
    interpret,
    optmElab,
    -- Compilable (..),
    convElab,
    interpElab,
    comp,
    optm2,
    optm,
    optmWithInput,
    conv,
    witn,
    execute,
  )
where

import Control.Arrow (left)
import Control.Monad (unless, when)
import qualified Data.Either as Either
import Data.Field.Galois (GaloisField)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Semiring (Semiring (one, zero))
import Keelung (Compilable (elaborate))
import qualified Keelung.Compiler.Compile as Compile
import Keelung.Compiler.Constraint (ConstraintSystem (..), numberOfConstraints)
import Keelung.Compiler.Error
import qualified Keelung.Compiler.Interpret as Interpret
import Keelung.Compiler.Optimise
import qualified Keelung.Compiler.Optimise.ConstantPropagation as ConstantPropagation
import qualified Keelung.Compiler.Optimise.Rewriting as Rewriting2
import Keelung.Compiler.R1CS
import Keelung.Compiler.Syntax.Untyped
import Keelung.Compiler.Util (Witness)
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Error (ElabError (..))
import Keelung.Field
import Keelung.Monad
import qualified Keelung.Syntax as K
import qualified Keelung.Syntax.Concrete as C

--------------------------------------------------------------------------------
-- Some top-level functions

erase :: (GaloisField n, Integral n, AcceptedField n, Compilable t) => Comp n (K.Val t n) -> Either ElabError (TypeErased n)
erase prog = elaborate prog >>= Rewriting2.run >>= return . eraseType

interpret :: (GaloisField n, Bounded n, Integral n, AcceptedField n, Compilable t) => Comp n (K.Val t n) -> [n] -> Either (Error n) [n]
interpret prog ins = left ElabError (elaborate prog) >>= \elab -> left InterpretError (Interpret.run elab ins)

interpElab :: (Show n, GaloisField n, Bounded n, Integral n, AcceptedField n) => C.Elaborated -> [n] -> Either String [n]
interpElab elab ins = left (show . InterpretError) (Interpret.run elab ins)

optmElab :: (Show n, GaloisField n, Bounded n, Integral n, AcceptedField n) => C.Elaborated -> Either (Error n) (ConstraintSystem n)
optmElab elab = do
  rewritten <- left ElabError (Rewriting2.run elab)
  return $ optimise $ Compile.run $ ConstantPropagation.run $ eraseType rewritten

convElab :: (GaloisField n, Bounded n, Integral n, AcceptedField n) => C.Elaborated -> Either (Error n) (R1CS n)
convElab xs = toR1CS <$> optmElab xs

-- elaboration => rewriting => type erasure => constant propagation => compilation
comp :: (GaloisField n, Bounded n, Integral n, AcceptedField n, Compilable t) => Comp n (K.Val t n) -> Either (Error n) (ConstraintSystem n)
comp prog = left ElabError (erase prog) >>= return . Compile.run . ConstantPropagation.run

-- elaboration => rewriting => type erasure => constant propagation => compilation => optimisation I
optm ::
  (GaloisField n, Bounded n, Integral n, AcceptedField n, Compilable t) =>
  Comp n (K.Val t n) ->
  Either (Error n) (ConstraintSystem n)
optm prog = comp prog >>= return . optimise

-- elaboration => rewriting => type erasure => constant propagation => compilation => optimisation I + II
optm2 ::
  (GaloisField n, Bounded n, Integral n, AcceptedField n, Compilable t) =>
  Comp n (K.Val t n) ->
  Either (Error n) (ConstraintSystem n)
optm2 prog = comp prog >>= return . optimise2 . optimise

-- with optimisation + partial evaluation with inputs
optmWithInput ::
  (GaloisField n, Bounded n, Integral n, AcceptedField n, Compilable t) =>
  Comp n (K.Val t n) ->
  [n] ->
  Either (Error n) (ConstraintSystem n)
optmWithInput program ins = do
  cs <- optm program
  let (_, cs') = optimiseWithInput ins cs
  return cs'

-- elaboration => rewriting => type erasure => constant propagation => compilation => optimisation => toR1CS
conv ::
  (GaloisField n, Bounded n, Integral n, AcceptedField n, Compilable t) =>
  Comp n (K.Val t n) ->
  Either (Error n) (R1CS n)
conv prog = comp prog >>= return . toR1CS . optimise

-- witn ::
-- (GaloisField n, Bounded n, Integral n) =>
-- Comp n (Expr t n) ->
-- Either String (R1CS n)
witn :: (GaloisField n, Bounded n, Integral n, AcceptedField n, Compilable t) => Comp n (K.Val t n) -> [n] -> Either (Error n) (Witness n)
witn prog ins = conv prog >>= left ExecError . witnessOfR1CS ins

-- | (1) Compile to R1CS.
--   (2) Generate a satisfying assignment, 'w'.
--   (3) Check whether 'w' satisfies the constraint system produced in (1).
--   (4) Check whether the R1CS result matches the interpreter result.
execute :: (GaloisField n, Bounded n, Integral n, AcceptedField n, Compilable t) => Comp n (K.Val t n) -> [n] -> Either (Error n) [n]
execute prog ins = do
  r1cs <- conv prog

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
