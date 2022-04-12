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
    Erase,
    interpret,
    eraseType,
    TypeErased (..),
    module Keelung.R1CS,
    module Keelung.Optimiser,
    Compilable (..),
    comp,
    optm,
    optmWithInput,
  )
where

import Data.Field.Galois (GaloisField)
import Data.Semiring (Semiring (one, zero))
import Keelung.Compile (compile)
import Keelung.Constraint (ConstraintSystem (..))
import Keelung.Interpret (interpret)
import Keelung.Monad
import Keelung.Optimiser
import qualified Keelung.Optimiser.ConstantPropagation as ConstantPropagation
import qualified Keelung.Optimiser.Rewriting as Rewriting
import Keelung.R1CS
import Keelung.Syntax
import Keelung.Syntax.Common
import Keelung.Syntax.Untyped (Erase, TypeErased (..), eraseType, eraseType')
import Keelung.Util (DebugGF (..))

--------------------------------------------------------------------------------
-- Some top-level functions

class Compilable n a where
  -- elaboration => rewriting => type erasure
  erase :: Comp n a -> Either String (TypeErased n)

instance (Erase ty, Num n) => Compilable n (Expr ty n) where
  erase prog = elaborate prog >>= Rewriting.run >>= return . eraseType

instance Num n => Compilable n () where
  erase prog = do
    ((), comp') <- runComp (Computation 0 0 mempty mempty mempty mempty mempty) prog
    return $ eraseType' comp'

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
