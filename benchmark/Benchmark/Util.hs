{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <&>" #-}

module Benchmark.Util where

import Data.ByteString (ByteString)
import Data.Serialize (Serialize, encode)
import Keelung (elaborate)
import Keelung.Compiler
import Keelung.Compiler.Optimize (elaborateAndRewrite)
import qualified Keelung.Compiler.Optimize.ConstantPropagation as ConstantPropagation
import Keelung.Monad (Comp)
import Keelung.Syntax (Val)

benchElaborate :: (Serialize n, Integral n) => Comp (Val t) -> ByteString
benchElaborate = encode . elaborate

benchRewrite :: (Integral n, Serialize n) => Comp (Val t) -> ByteString
benchRewrite = encode . elaborateAndRewrite

benchInterpret :: (Serialize n, GaloisField n, Integral n) => Comp (Val t) -> [n] -> ByteString
benchInterpret prog = encode . interpret prog

benchEraseType :: (GaloisField n, Bounded n, Integral n) => Comp (Val t) -> String
benchEraseType prog = show $ erase prog

benchPropogateConstant :: (GaloisField n, Bounded n, Integral n) => Comp (Val t) -> String
benchPropogateConstant prog = show $ erase prog >>= return . ConstantPropagation.run

benchCompile :: (GaloisField n, Bounded n, Integral n, Show n) => Comp (Val t) -> String
benchCompile prog = show $ compile prog

benchOptimize :: (GaloisField n, Bounded n, Integral n, Show n) => Comp (Val t) -> String
benchOptimize prog = show $ optimize prog

benchOptimize2 :: (GaloisField n, Bounded n, Integral n, Show n) => Comp (Val t) -> String
benchOptimize2 prog = show $ optimize2 prog

benchOptimizeWithInput :: (GaloisField n, Bounded n, Integral n, Show n) => Comp (Val t) -> [n] -> String
benchOptimizeWithInput prog = show . optimizeWithInput prog

-- -- This function "executes" the comp two ways, once by interpreting
-- -- the resulting TExp and second by interpreting the resulting circuit
-- -- on the inputs provided. Both results are checked to match 'res'.
-- -- The function outputs a 'Result' that details number of variables and
-- -- constraints in the resulting constraint system.
-- compareWithResult ::
--   (Typeable ty, GaloisField a, Serialize a, Bounded a, Integral a) => SimplParam -> Comp (Val t) -> [a] -> a -> Bool
-- compareWithResult flag prog inputs output =
--   case execute flag prog inputs of
--     Left _ -> False
--     Right result -> resultResult result == output
