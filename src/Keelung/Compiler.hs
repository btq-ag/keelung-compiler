{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Compiler
  ( module Keelung.Compiler.Monad,
    module Keelung.Compiler.Syntax,
    module Keelung.Compiler.Error,
    GaloisField,
    Semiring (one, zero),
    module Prelude,
    compile,
    ConstraintSystem (..),
    numberOfConstraints,
    Erase,
    eraseType,
    TypeErased (..),
    module Keelung.Compiler.R1CS,
    module Keelung.Compiler.Optimise,
    Compilable (..),
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
import Control.Monad (when)
import Data.Field.Galois (GaloisField)
import qualified Data.IntMap as IntMap
import Data.Semiring (Semiring (one, zero))
import Keelung.Compiler.Compile (compile)
import Keelung.Compiler.Constraint (ConstraintSystem (..), numberOfConstraints)
import Keelung.Compiler.Error
import Keelung.Compiler.Interpret
import Keelung.Compiler.Monad
import Keelung.Compiler.Optimise
import qualified Keelung.Compiler.Optimise.ConstantPropagation as ConstantPropagation
import qualified Keelung.Compiler.Optimise.Rewriting as Rewriting
import Keelung.Compiler.R1CS
import Keelung.Compiler.Syntax
import Keelung.Compiler.Syntax.Untyped (Erase, TypeErased (..), eraseType)
import Keelung.Compiler.Util (Witness)

--------------------------------------------------------------------------------
-- Some top-level functions

class Compilable n a where
  -- elaboration => rewriting => type erasure
  erase :: Comp n a -> Either String (TypeErased n)
  interpret :: Comp n a -> [n] -> Either (Error n) (Maybe n)

instance (Erase ty, Num n, GaloisField n, Bounded n, Integral n, Elaborable ty) => Compilable n (Expr ty n) where
  erase prog = elaborate prog >>= Rewriting.run >>= return . eraseType
  interpret prog inputs = left OtherError (elaborate prog) >>= \elab -> left InterpretError (interpretElaborated elab inputs)

instance (Num n, GaloisField n, Bounded n, Integral n) => Compilable n () where
  erase prog = elaborate_ prog >>= Rewriting.run >>= return . eraseType
  interpret prog inputs = left OtherError (elaborate_ prog) >>= \elab -> left InterpretError (interpretElaborated elab inputs)

-- elaboration => rewriting => type erasure => constant propagation => compilation
comp :: (Compilable n a, GaloisField n, Bounded n, Integral n) => Comp n a -> Either (Error n) (ConstraintSystem n)
comp prog = left OtherError (erase prog) >>= return . compile . ConstantPropagation.run

-- elaboration => rewriting => type erasure => constant propagation => compilation => optimisation I
optm ::
  (Compilable n a, GaloisField n, Bounded n, Integral n) =>
  Comp n a ->
  Either (Error n) (ConstraintSystem n)
optm prog = comp prog >>= return . optimise

-- elaboration => rewriting => type erasure => constant propagation => compilation => optimisation I + II
optm2 ::
  (Compilable n a, GaloisField n, Bounded n, Integral n) =>
  Comp n a ->
  Either (Error n) (ConstraintSystem n)
optm2 prog = comp prog >>= return . optimise2 . optimise

-- with optimisation + partial evaluation with inputs
optmWithInput ::
  (Compilable n a, GaloisField n, Bounded n, Integral n) =>
  Comp n a ->
  [n] ->
  Either (Error n) (ConstraintSystem n)
optmWithInput program input = do
  cs <- optm program
  let (_, cs') = optimiseWithInput input cs
  return cs'

-- elaboration => rewriting => type erasure => constant propagation => compilation => optimisation => toR1CS
conv ::
  (Compilable n a, GaloisField n, Bounded n, Integral n) =>
  Comp n a ->
  Either (Error n) (R1CS n)
conv prog = comp prog >>= return . toR1CS . optimise

-- witn ::
-- (Compilable n a, GaloisField n, Bounded n, Integral n) =>
-- Comp n a ->
-- Either String (R1CS n)
witn :: (Compilable n a, GaloisField n, Bounded n, Integral n) => Comp n a -> [n] -> Either (Error n) (Witness n)
witn prog inputs = conv prog >>= left ExecError . witnessOfR1CS inputs

-- | (1) Compile to R1CS.
--   (2) Generate a satisfying assignment, 'w'.
--   (3) Check whether 'w' satisfies the constraint system produced in (1).
--   (4) Check whether the R1CS result matches the interpreter result.
execute :: (Compilable n a, GaloisField n, Bounded n, Integral n) => Comp n a -> [n] -> Either (Error n) (Maybe n)
execute prog inputs = do
  r1cs <- conv prog

  let outputVar = r1csOutputVar r1cs
  actualWitness <- left ExecError $ witnessOfR1CS inputs r1cs

  -- extract the output value from the witness
  actualOutput <- case outputVar of
    Nothing -> return Nothing
    Just var -> case IntMap.lookup var actualWitness of
      Nothing ->
        Left $
          ExecError $
            ExecOutputVarNotMappedError outputVar actualWitness
      Just value -> return $ Just value

  -- interpret the program to see if the output value is correct
  expectedOutput <- interpret prog inputs

  when (actualOutput /= expectedOutput) $ do
    Left $ ExecError $ ExecOutputError expectedOutput actualOutput

  case satisfyR1CS actualWitness r1cs of
    Nothing -> return ()
    Just r1c's ->
      Left $
        ExecError $
          ExecR1CUnsatisfiableError r1c's actualWitness

  return actualOutput
