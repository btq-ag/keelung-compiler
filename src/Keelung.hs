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
    comp,
    comp1,
    elab,
    elab',
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
import Keelung.Syntax.Untyped (Erase, TypeErased (..), eraseType)
import Keelung.Util (DebugGF (..))

--------------------------------------------------------------------------------
-- Some top-level functions

-- just elaborate & erase types
elab :: (Erase ty, Num n) => Comp n (Expr ty n) -> Either String (TypeErased n)
elab program = fmap eraseType (elaborate program)

-- elaborate & erase types & rewrite 
elab' :: (Erase ty, Num n) => Comp n (Expr ty n) -> Either String (TypeErased n)
elab' program = fmap eraseType (elaborate program >>= Rewriting.run)

comp1 :: (GaloisField n, Erase ty, Bounded n, Integral n) => Comp n (Expr ty n) -> Either String (ConstraintSystem n)
comp1 program = elaborate program >>= return . compile . ConstantPropagation.run . eraseType

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
