{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung
  ( module Keelung.Monad,
    module Keelung.Syntax,
    module Keelung.Error,
    module Keelung.Syntax.Common,
    GaloisField,
    DebugGF (..),
    Semiring (one, zero),
    module Prelude,
    compile,
    ConstraintSystem (..),
    numberOfConstraints,
    Erase,
    eraseType,
    TypeErased (..),
    module Keelung.R1CS,
    module Keelung.Optimise,
    Compilable (..),
    comp,
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
import Keelung.Compile (compile)
import Keelung.Constraint (ConstraintSystem (..), numberOfConstraints)
import Keelung.Error
import Keelung.Interpret
import Keelung.Monad
import Keelung.Optimise
import qualified Keelung.Optimise.ConstantPropagation as ConstantPropagation
import qualified Keelung.Optimise.Rewriting as Rewriting
import Keelung.R1CS
import Keelung.Syntax
import Keelung.Syntax.Common
import Keelung.Syntax.Untyped (Erase, TypeErased (..), eraseType)
import Keelung.Util (DebugGF (..))


--------------------------------------------------------------------------------
-- Some top-level functions

class Compilable n a where
  -- elaboration => rewriting => type erasure
  erase :: Comp n a -> Either String (TypeErased n)
  interpret :: Comp n a -> [n] -> Either String (Maybe n)

instance (Erase ty, Num n, GaloisField n, Bounded n, Integral n) => Compilable n (Expr ty n) where
  erase prog = elaborate prog >>= Rewriting.run >>= return . eraseType
  interpret = interpretExpr

instance (Num n, GaloisField n, Bounded n, Integral n) => Compilable n () where
  erase prog = elaborate' prog >>= Rewriting.run >>= return . eraseType
  interpret = interpretProc

-- elaboration => rewriting => type erasure => constant propagation => compilation
comp :: (Compilable n a, GaloisField n, Bounded n, Integral n) => Comp n a -> Either (Error n) (ConstraintSystem n)
comp prog = left OtherError (erase prog) >>= return . compile . ConstantPropagation.run

-- elaboration => rewriting => type erasure => constant propagation => compilation => optimisation
optm ::
  (Compilable n a, GaloisField n, Bounded n, Integral n) =>
  Comp n a ->
  Either (Error n) (ConstraintSystem n)
optm prog = comp prog >>= return . optimise

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
  expectedOutput <- left OtherError $ interpret prog inputs

  when (actualOutput /= expectedOutput) $ do
    Left $ ExecError $ ExecOutputError expectedOutput actualOutput

  case satisfyR1CS actualWitness r1cs of
    Nothing -> return ()
    Just r1c's ->
      Left $
        ExecError $
          ExecR1CUnsatisfiableError r1c's actualWitness

  return actualOutput
