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
import Control.Monad (when)
import Data.Field.Galois (GaloisField)
import qualified Data.IntMap as IntMap
import Data.Semiring (Semiring (one, zero))
import Data.Typeable (Typeable)
import Keelung (elaborateAndFlatten)
import qualified Keelung.Compiler.Compile as Compile
import Keelung.Compiler.Constraint (ConstraintSystem (..), numberOfConstraints)
import Keelung.Compiler.Error
import Keelung.Compiler.Interpret
import Keelung.Compiler.Optimise
import qualified Keelung.Compiler.Optimise.ConstantPropagation as ConstantPropagation
import qualified Keelung.Compiler.Optimise.Rewriting as Rewriting2
import Keelung.Compiler.R1CS
import Keelung.Compiler.Syntax.Untyped
import Keelung.Compiler.Util (Witness)
import Keelung.Field
import Keelung.Monad
import qualified Keelung.Syntax as K
import qualified Keelung.Syntax.Concrete as C

--------------------------------------------------------------------------------
-- Some top-level functions

erase :: (GaloisField n, Integral n, AcceptedField n, Typeable kind) => Comp n (K.Expr kind n) -> Either String (TypeErased n)
erase prog = elaborateAndFlatten prog >>= Rewriting2.run >>= return . eraseType

interpret :: (GaloisField n, Bounded n, Integral n, Typeable kind, AcceptedField n) => Comp n (K.Expr kind n) -> [n] -> Either (Error n) (Maybe n)
interpret prog inputs = left OtherError (elaborateAndFlatten prog) >>= \elab -> left InterpretError (interpretElaborated2 elab inputs)

interpElab :: (Show n, GaloisField n, Bounded n, Integral n, AcceptedField n) => C.Elaborated ->  [n] -> Either String (Maybe n)
interpElab elab inputs = left (show . InterpretError) (interpretElaborated2 elab inputs)

optmElab :: (Show n, GaloisField n, Bounded n, Integral n, AcceptedField n) => C.Elaborated -> Either (Error n) (ConstraintSystem n)
-- optmElab (Left err) = Left (OtherError err)
optmElab elab = do
  rewritten <- left OtherError (Rewriting2.run elab)
  return $ optimise $ Compile.run $ ConstantPropagation.run $ eraseType rewritten

-- optmElab :: (Show n, GaloisField n, Bounded n, Integral n, AcceptedField n) => Either String C.Elaborated -> Either (Error n) (ConstraintSystem n)
-- optmElab (Left err) = Left (OtherError err)
-- optmElab (Right elab) = do
--   rewritten <- left OtherError (Rewriting2.run elab)
--   return $ optimise $ Compile.run $ ConstantPropagation.run $ eraseType rewritten

-- class Compilable n where
--   optmElab2 :: (Show n, GaloisField n, Bounded n, Integral n, AcceptedField n) => Either String C.Elaborated -> Either (Error n) (ConstraintSystem n)
--   convElab2 :: (GaloisField n, Bounded n, Integral n, AcceptedField n) => Either String C.Elaborated -> Either (Error n) (R1CS n)

-- instance Compilable B64 where
--   optmElab2 = optmElab
--   convElab2 = convElab

-- instance Compilable GF181 where
--   optmElab2 = optmElab
--   convElab2 = convElab

-- instance Compilable BN128 where
--   optmElab2 = optmElab
--   convElab2 = convElab

convElab :: (GaloisField n, Bounded n, Integral n, AcceptedField n) => C.Elaborated -> Either (Error n) (R1CS n)
convElab xs = toR1CS <$> optmElab xs

-- elaboration => rewriting => type erasure => constant propagation => compilation
comp :: (GaloisField n, Bounded n, Integral n, AcceptedField n, Typeable kind) => Comp n (K.Expr kind n) -> Either (Error n) (ConstraintSystem n)
comp prog = left OtherError (erase prog) >>= return . Compile.run . ConstantPropagation.run

-- elaboration => rewriting => type erasure => constant propagation => compilation => optimisation I
optm ::
  (GaloisField n, Bounded n, Integral n, AcceptedField n, Typeable kind) =>
  Comp n (K.Expr kind n) ->
  Either (Error n) (ConstraintSystem n)
optm prog = comp prog >>= return . optimise

-- elaboration => rewriting => type erasure => constant propagation => compilation => optimisation I + II
optm2 ::
  (GaloisField n, Bounded n, Integral n, AcceptedField n, Typeable kind) =>
  Comp n (K.Expr kind n) ->
  Either (Error n) (ConstraintSystem n)
optm2 prog = comp prog >>= return . optimise2 . optimise

-- with optimisation + partial evaluation with inputs
optmWithInput ::
  (GaloisField n, Bounded n, Integral n, AcceptedField n, Typeable kind) =>
  Comp n (K.Expr kind n) ->
  [n] ->
  Either (Error n) (ConstraintSystem n)
optmWithInput program input = do
  cs <- optm program
  let (_, cs') = optimiseWithInput input cs
  return cs'

-- elaboration => rewriting => type erasure => constant propagation => compilation => optimisation => toR1CS
conv ::
  (GaloisField n, Bounded n, Integral n, AcceptedField n, Typeable kind) =>
  Comp n (K.Expr kind n) ->
  Either (Error n) (R1CS n)
conv prog = comp prog >>= return . toR1CS . optimise

-- witn ::
-- (GaloisField n, Bounded n, Integral n) =>
-- Comp n (Expr kind n) ->
-- Either String (R1CS n)
witn :: (GaloisField n, Bounded n, Integral n, AcceptedField n, Typeable kind) => Comp n (K.Expr kind n) -> [n] -> Either (Error n) (Witness n)
witn prog inputs = conv prog >>= left ExecError . witnessOfR1CS inputs

-- | (1) Compile to R1CS.
--   (2) Generate a satisfying assignment, 'w'.
--   (3) Check whether 'w' satisfies the constraint system produced in (1).
--   (4) Check whether the R1CS result matches the interpreter result.
execute :: (GaloisField n, Bounded n, Integral n, AcceptedField n, Typeable kind) => Comp n (K.Expr kind n) -> [n] -> Either (Error n) (Maybe n)
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
