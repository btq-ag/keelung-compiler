{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Benchmark.Keelung where

import Data.ByteString (ByteString)
import Data.Serialize (Serialize, encode)
import Data.Typeable (Typeable)
import Keelung (elaborate)
import Keelung.Compiler
import qualified Keelung.Compiler.Optimise.ConstantPropagation as ConstantPropagation
import Keelung.Monad
import Keelung.Syntax

benchElaborate :: (Typeable kind, Serialize n, GaloisField n, Bounded n, Integral n) => Comp n (Expr kind n) -> ByteString
benchElaborate = encode . elaborate

benchRewrite :: (GaloisField n, Bounded n, Integral n, Serialize n, Typeable kind) => Comp n (Expr kind n) -> ByteString
benchRewrite = encode . elaborateAndRewrite
  
benchInterpret :: (GaloisField n, Show n, Bounded n, Integral n, Fractional n, Typeable kind) => Comp n (Expr kind n) -> [n] -> String
benchInterpret prog input =
  show $ interpret prog input

benchEraseType :: (GaloisField n, Num n, Show n, Bounded n, Integral n, Fractional n, Typeable kind) => Comp n (Expr kind n) -> String
benchEraseType prog = show $ erase prog

benchPropogateConstant :: (GaloisField n, Bounded n, Integral n, Typeable kind) => Comp n (Expr kind n) -> String
benchPropogateConstant prog = show $ erase prog >>= return . ConstantPropagation.run

benchCompile :: (GaloisField n, Bounded n, Integral n, Show n, Typeable kind) => Comp n (Expr kind n) -> String
benchCompile prog = show $ comp prog

benchOptimise :: (GaloisField n, Bounded n, Integral n, Show n, Typeable kind) => Comp n (Expr kind n) -> String
benchOptimise prog = show $ optm prog

benchOptimise2 :: (GaloisField n, Bounded n, Integral n, Show n, Typeable kind) => Comp n (Expr kind n) -> String
benchOptimise2 prog = show $ optm2 prog

benchOptimiseWithInput :: (GaloisField n, Bounded n, Integral n, Show n, Typeable kind) => Comp n (Expr kind n) -> [n] -> String
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
