{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}

module Benchmark.Keelung where

import Keelung
import qualified Keelung.Syntax.Untyped as Untyped
import qualified Keelung.Optimiser.ConstantPropagation as ConstantPropagation

benchElaborate :: Comp ty a -> Int
benchElaborate prog = case elaborate prog of
  Left _ -> -1
  Right elab -> toNumber $ elabExpr elab
  where
    toNumber :: Expr ty a -> Int
    toNumber !te = case te of
      Val _ -> 0
      Var _ -> 1
      Add _ _-> 2
      Sub _ _-> 3
      Mul _ _-> 4
      Div _ _-> 5
      Eq _ _-> 6
      And _ _-> 7
      Or _ _-> 8
      Xor _ _-> 9
      BEq _ _-> 10
      IfThenElse {} -> 11
      ToBool _ -> 12
      ToNum _ -> 13

benchInterpret :: (Show a, GaloisField a) => Comp ty a -> [a] -> String
benchInterpret prog input = 
  show $ elaborate prog >>= \elab -> interpret elab input

benchEraseType :: (Erase ty, Num a) => Comp ty a -> Int
benchEraseType prog = case elaborate prog of
  Left _ -> -1
  Right elab -> toNumber $ erasedExpr $  eraseType elab
  where
    toNumber :: Untyped.Expr a -> Int
    toNumber !te = case te of
      Untyped.Var _ -> 0
      Untyped.Val _ -> 1
      Untyped.BinOp _ _ -> 2
      Untyped.IfThenElse {} -> 3
      

benchPropogateConstant :: (GaloisField a, Bounded a, Integral a, Erase ty) => Comp ty a -> Int 
benchPropogateConstant prog = case elaborate prog of
  Left _ -> -1 
  Right elab -> toNumber $ erasedExpr $ ConstantPropagation.run $ eraseType elab
  where
    toNumber :: Untyped.Expr a -> Int
    toNumber !te = case te of
      Untyped.Var _ -> 0
      Untyped.Val _ -> 1
      Untyped.BinOp _ _ -> 2
      Untyped.IfThenElse {} -> 3

benchCompile :: (GaloisField a, Bounded a, Integral a, Erase ty) => Comp ty a -> String
benchCompile prog = case elaborate prog of
  Left _ -> ""
  Right elab -> show $ compile $ eraseType elab

benchOptimise :: (GaloisField a, Bounded a, Integral a, Erase ty) => Comp ty a -> String
benchOptimise prog = case elaborate prog of
  Left _ -> ""
  Right elab -> show $ optimise $ compile $ ConstantPropagation.run $ eraseType elab

benchOptimiseWithInput :: (GaloisField a, Bounded a, Integral a, Erase ty) => Comp ty a -> [a] -> String
benchOptimiseWithInput prog input = case elaborate prog of
  Left _ -> ""
  Right elab -> show $ optimiseWithInput input $ compile $ ConstantPropagation.run $ eraseType elab

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
