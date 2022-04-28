{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung
  ( module Keelung.Monad,
    module Keelung.Syntax,
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
    conv
  )
where

import Data.Field.Galois (GaloisField)
import Data.Semiring (Semiring (one, zero))
import Keelung.Compile (compile)
import Keelung.Constraint (ConstraintSystem (..), numberOfConstraints)
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

instance (Erase ty, Num n, GaloisField n) => Compilable n (Expr ty n) where
  erase prog = elaborate prog >>= Rewriting.run >>= return . eraseType
  interpret = interpretExpr

instance (Num n, GaloisField n) => Compilable n () where
  erase prog = elaborate' prog >>= Rewriting.run >>= return . eraseType
  interpret = interpretProc

-- elaboration => rewriting => type erasure => constant propagation => compilation
comp :: (Compilable n a, GaloisField n, Bounded n, Integral n) => Comp n a -> Either String (ConstraintSystem n)
comp prog = erase prog >>= return . compile . ConstantPropagation.run

-- elaboration => rewriting => type erasure => constant propagation => compilation => optimisation
optm ::
  (Compilable n a, GaloisField n, Bounded n, Integral n) =>
  Comp n a ->
  Either String (ConstraintSystem n)
optm prog = comp prog >>= return . optimise

-- with optimisation + partial evaluation with inputs
optmWithInput ::
  (Compilable n a, GaloisField n, Bounded n, Integral n) =>
  Comp n a ->
  [n] ->
  Either String (ConstraintSystem n)
optmWithInput program input = do
  cs <- optm program
  let (_, cs') = optimiseWithInput input cs
  return cs'

-- elaboration => rewriting => type erasure => constant propagation => compilation => optimisation => toR1CS
conv ::
  (Compilable n a, GaloisField n, Bounded n, Integral n) =>
  Comp n a ->
  Either String (R1CS n)
conv prog = comp prog >>= return . toR1CS . optimise
