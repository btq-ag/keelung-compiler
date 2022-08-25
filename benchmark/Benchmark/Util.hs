{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <&>" #-}

module Benchmark.Util where

import Data.ByteString (ByteString)
import Data.Serialize (Serialize, encode)
import Keelung (AcceptedField, elaborate)
import Keelung.Compiler
import Keelung.Compiler.Optimize (elaborateAndRewrite)
import qualified Keelung.Compiler.Optimize.ConstantPropagation as ConstantPropagation
import Keelung.Monad (Comp)
import Keelung.Syntax (Val)

benchElaborate :: (AcceptedField n, Serialize n, Integral n) => Comp n (Val t n) -> ByteString
benchElaborate = encode . elaborate

benchRewrite :: (AcceptedField n, Integral n, Serialize n) => Comp n (Val t n) -> ByteString
benchRewrite = encode . elaborateAndRewrite

benchInterpret :: (AcceptedField n, Serialize n, GaloisField n, Integral n) => Comp n (Val t n) -> [n] -> ByteString
benchInterpret prog = encode . interpret prog

benchEraseType :: (AcceptedField n, GaloisField n, Bounded n, Integral n) => Comp n (Val t n) -> String
benchEraseType prog = show $ erase prog

benchPropogateConstant :: (AcceptedField n, GaloisField n, Bounded n, Integral n) => Comp n (Val t n) -> String
benchPropogateConstant prog = show $ erase prog >>= return . ConstantPropagation.run

benchCompile :: (AcceptedField n, GaloisField n, Bounded n, Integral n, Show n) => Comp n (Val t n) -> String
benchCompile prog = show $ compile prog

benchOptimize :: (AcceptedField n, GaloisField n, Bounded n, Integral n, Show n) => Comp n (Val t n) -> String
benchOptimize prog = show $ optimize prog

benchOptimize2 :: (AcceptedField n, GaloisField n, Bounded n, Integral n, Show n) => Comp n (Val t n) -> String
benchOptimize2 prog = show $ optimize2 prog

benchOptimizeWithInput :: (AcceptedField n, GaloisField n, Bounded n, Integral n, Show n) => Comp n (Val t n) -> [n] -> String
benchOptimizeWithInput prog = show . optimizeWithInput prog

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
