{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Benchmark.Keelung where

import Data.ByteString (ByteString)
import Data.Serialize (Serialize, encode)
import Data.Typeable (Typeable)
import Keelung (elaborate, AcceptedField)
import Keelung.Compiler
import qualified Keelung.Compiler.Optimize.ConstantPropagation as ConstantPropagation
import Keelung.Monad
import Keelung.Syntax

import Keelung.Compiler.Optimize (elaborateAndRewrite)

benchElaborate :: (AcceptedField n,  Serialize n, GaloisField n, Bounded n, Integral n) => Comp n (Val kind n) -> ByteString
benchElaborate = encode . elaborate

benchRewrite :: (AcceptedField n,GaloisField n, Bounded n, Integral n, Serialize n) => Comp n (Val kind n) -> ByteString
benchRewrite = encode . elaborateAndRewrite
  
benchInterpret :: (AcceptedField n,GaloisField n, Show n, Bounded n, Integral n, Fractional n) => Comp n (Val kind n) -> [n] -> String
benchInterpret prog input =
  show $ interpret prog input

benchEraseType :: (AcceptedField n,GaloisField n, Num n, Show n, Bounded n, Integral n, Fractional n) => Comp n (Val kind n) -> String
benchEraseType prog = show $ erase prog

benchPropogateConstant :: (AcceptedField n,GaloisField n, Bounded n, Integral n) => Comp n (Val kind n) -> String
benchPropogateConstant prog = show $ erase prog >>= return . ConstantPropagation.run

benchCompile :: (AcceptedField n,GaloisField n, Bounded n, Integral n, Show n) => Comp n (Val kind n) -> String
benchCompile prog = show $ compile prog

benchOptimize :: (AcceptedField n,GaloisField n, Bounded n, Integral n, Show n) => Comp n (Val kind n) -> String
benchOptimize prog = show $ optimize prog

benchOptimize2 :: (AcceptedField n,GaloisField n, Bounded n, Integral n, Show n) => Comp n (Val kind n) -> String
benchOptimize2 prog = show $ optimize2 prog

benchOptimizeWithInput :: (AcceptedField n,GaloisField n, Bounded n, Integral n, Show n) => Comp n (Val kind n) -> [n] -> String
benchOptimizeWithInput prog input = show $ optimizeWithInput prog input

-- -- This function "executes" the comp two ways, once by interpreting
-- -- the resulting TExp and second by interpreting the resulting circuit
-- -- on the inputs provided. Both results are checked to match 'res'.
-- -- The function outputs a 'Result' that details number of variables and
-- -- constraints in the resulting constraint system.
-- compareWithResult ::
--   (Typeable ty, GaloisField a, Serialize a, Bounded a, Integral a) => SimplParam -> Comp n (Val ty n) -> [a] -> a -> Bool
-- compareWithResult flag prog inputs output =
--   case execute flag prog inputs of
--     Left _ -> False
--     Right result -> resultResult result == output
