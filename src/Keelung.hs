{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <&>" #-}

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
    erase,
    erase',
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

-- elaborate = elaborate


-- elaboration => type erasure 
-- erase :: (Erase ty, Num n) => Comp n (Expr ty n) -> Either String (TypeErased n)
-- erase program = fmap eraseType (elaborate program)

-- elaboration => rewriting => type erasure
erase :: (Erase ty, Num n) => Comp n (Expr ty n) -> Either String (TypeErased n)
erase prog = fmap eraseType (elaborate prog >>= Rewriting.run)

erase' :: (Num n) => Comp n () -> Either String (TypeErased n)
erase' prog = do
  ((), comp') <- runComp (Computation 0 0 mempty mempty mempty mempty mempty) prog
  return $ eraseType' comp'

-- elaboration => rewriting => type erasure => constant propagation => compilation
-- compC :: (GaloisField n, Erase ty, Bounded n, Integral n) => Comp n (Expr ty n) -> Either String (ConstraintSystem n)
-- compC program = elaborate program >>= return . compile . ConstantPropagation.run . eraseType

comp :: (GaloisField n, Erase ty, Bounded n, Integral n) => Comp n (Expr ty n) -> Either String (ConstraintSystem n)
comp program = elaborate program >>= Rewriting.run >>= return . compile . ConstantPropagation.run . eraseType

-- with optimisation
optm :: (GaloisField n, Erase ty, Bounded n, Integral n) => Comp n (Expr ty n) -> Either String (ConstraintSystem n)
optm program = optimise <$> comp program

-- with optimisation + partial evaluation with inputs
optmWithInput :: (GaloisField n, Bounded n, Integral n, Erase ty) => Comp n (Expr ty n) -> [n] -> Either String (ConstraintSystem n)
optmWithInput program input = do
  cs <- optm program
  let (_, cs') = optimiseWithInput input cs
  return cs'
