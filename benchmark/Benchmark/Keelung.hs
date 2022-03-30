{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE BangPatterns #-}

module Benchmark.Keelung where

import Keelung
import qualified Keelung.Optimiser.ConstantPropagation as ConstantPropagation

benchElaborate :: (GaloisField a, Bounded a, Integral a) => Comp ty a -> Int
benchElaborate prog =
  case elaborate prog of
    Left _ -> -1
    Right elab -> toNumber $ elabExpr elab
      where
        toNumber :: Expr ty a -> Int
        toNumber !te = case te of
          Val _ -> 0
          Var _ -> 1
          Add _ _ -> 2
          Sub _ _ -> 3
          Mul _ _ -> 4
          Div _ _ -> 5
          Eq _ _ -> 6
          And _ _ -> 7
          Or _ _ -> 8
          Xor _ _ -> 9
          BEq _ _ -> 10
          IfThenElse {} -> 11
          ToBool _ -> 12
          ToNum _ -> 13

benchInterpret :: (Show a, GaloisField a) => Comp ty a -> [a] -> String
benchInterpret prog input =
  show $ elaborate prog >>= \elab -> interpret elab input

benchEraseType :: (Erase ty, Num a, Show a, Bounded a, Integral a, Fractional a) => Comp ty a -> String
benchEraseType prog =
  show $ elaborate prog >>= return . eraseType

benchPropogateConstant :: (GaloisField a, Bounded a, Integral a, Erase ty) => Comp ty a -> String
benchPropogateConstant prog =
  show $ elaborate prog >>= return . ConstantPropagation.run . eraseType

benchCompile :: (GaloisField a, Bounded a, Integral a, Erase ty) => Comp ty a -> String
benchCompile prog =
  show $ elaborate prog >>= return . compile . eraseType

benchOptimise :: (GaloisField a, Bounded a, Integral a, Erase ty) => Comp ty a -> String
benchOptimise prog =
  show $ elaborate prog >>= return . optimise . compile . ConstantPropagation.run . eraseType

benchOptimiseWithInput :: (GaloisField a, Bounded a, Integral a, Erase ty) => Comp ty a -> [a] -> String
benchOptimiseWithInput prog input =
  show $ elaborate prog >>= return . optimiseWithInput input . compile . ConstantPropagation.run . eraseType

-- -- This function "executes" the comp two ways, once by interpreting
-- -- the resulting TExp and second by interpreting the resulting circuit
-- -- on the inputs provided. Both results are checked to match 'res'.
-- -- The function outputs a 'Result' that details number of variables and
-- -- constraints in the resulting constraint system.
-- compareWithResult ::
--   (Typeable ty, GaloisField a, Serialize a, Bounded a, Integral a) => SimplParam -> Comp ty a -> [a] -> a -> Bool
-- compareWithResult flag prog inputs output =
--   case execute flag prog inputs of
--     Left _ -> False
--     Right result -> resultResult result == output
