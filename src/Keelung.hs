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
    ConstraintSystem(..),
    Erase,
    interpret,
    eraseType,
    TypeErased(..),
    module Keelung.R1CS,
    module Keelung.Optimiser,
    comp,
    elab,
    optm,
    optmWithInput
  )
where

import Data.Field.Galois (GaloisField)
import Data.Semiring (Semiring (one, zero))
import Keelung.Syntax.Common
import Keelung.Monad
import Keelung.Syntax
import Keelung.Compile (compile)
import Keelung.Util (DebugGF (..))
import Keelung.Constraint (ConstraintSystem(..))
import Keelung.Syntax.Untyped (Erase, eraseType, TypeErased (..))
import Keelung.Interpret (interpret)
import Keelung.R1CS
import Keelung.Optimiser
import qualified Keelung.Optimiser.ConstantPropagation as ConstantPropagation


--------------------------------------------------------------------------------
-- Some top-level functions

-- just elaborate & erase types 
elab :: (Erase ty, Num n) => Comp ty n -> Either String (TypeErased n)
elab program = fmap eraseType (elaborate program)

-- without optimisation (but with constant propagation)
comp :: (GaloisField n, Erase ty, Bounded n, Integral n) => Comp ty n -> Either String (ConstraintSystem n)
comp program = elaborate program >>= return . compile . ConstantPropagation.run . eraseType

-- with optimisation 
optm :: (GaloisField n, Erase ty, Bounded n, Integral n) => Comp ty n -> Either String (ConstraintSystem n)
optm program = optimise <$> comp program

-- with optimisation + partial evaluation with inputs
optmWithInput :: (GaloisField n, Bounded n, Integral n, Erase ty) => Comp ty n -> [n] -> Either String (ConstraintSystem n)
optmWithInput program input = do
  cs <- optm program
  let (_, cs') = optimiseWithInput input cs
  return cs'
