{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Benchmark.Keelung where

import Keelung.Compiler
import Keelung.Monad
import Keelung (elaborate)
import Keelung.Syntax 
import qualified Keelung.Compiler.Optimise.ConstantPropagation as ConstantPropagation

benchElaborate :: (GaloisField n, Bounded n, Integral n) => Comp n (Expr ty n) -> Int
benchElaborate prog =
  case elaborate prog of
    Left _ -> -1
    Right elaborated -> case elabExpr elaborated of
      Nothing -> -2
      Just n -> toNumber n
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


benchRewrite :: (GaloisField n, Bounded n, Integral n) => Comp n (Expr kind n) -> Int
benchRewrite prog =
  case elaborateAndRewrite prog of
    Left _ -> -1
    Right elaborated -> case elabExpr elaborated of
      Nothing -> -2
      Just n -> toNumber n
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

benchInterpret :: (GaloisField n, Show n, Bounded n, Integral n, Fractional n) => Comp n (Expr kind n) -> [n] -> String
benchInterpret prog input =
  show $ interpret prog input

benchEraseType :: (GaloisField n, Num n, Show n, Bounded n, Integral n, Fractional n, Erase kind) => Comp n (Expr kind n) -> String
benchEraseType prog = show $ erase prog

benchPropogateConstant :: (GaloisField n, Bounded n, Integral n, Erase kind) => Comp n (Expr kind n) -> String
benchPropogateConstant prog = show $ erase prog >>= return . ConstantPropagation.run

benchCompile :: (GaloisField n, Bounded n, Integral n, Show n, Erase kind) => Comp n (Expr kind n) -> String
benchCompile prog = show $ comp prog

benchOptimise :: (GaloisField n, Bounded n, Integral n, Show n, Erase kind) => Comp n (Expr kind n) -> String
benchOptimise prog = show $ optm prog

benchOptimise2 :: (GaloisField n, Bounded n, Integral n, Show n, Erase kind) => Comp n (Expr kind n) -> String
benchOptimise2 prog = show $ optm2 prog

benchOptimiseWithInput :: (GaloisField n, Bounded n, Integral n, Show n, Erase kind) => Comp n (Expr kind n) -> [n] -> String
benchOptimiseWithInput prog input = show $ optmWithInput prog input

-- -- This function "executes" the comp two ways, once by interpreting
-- -- the resulting TExp and second by interpreting the resulting circuit
-- -- on the inputs provided. Both results are checked to match 'res'.
-- -- The function outputs a 'Result' that details number of variables and
-- -- constraints in the resulting constraint system.
-- compareWithResult ::
--   (Typeable ty, GaloisField a, Serialize a, Bounded a, Integral a) => SimplParam -> Comp n (Expr ty n) -> [a] -> a -> Bool
-- compareWithResult flag prog inputs output =
--   case execute flag prog inputs of
--     Left _ -> False
--     Right result -> resultResult result == output
