{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Experiment (tests, run) where

import Keelung hiding (compile)
import Keelung.Compiler.Options
import Test.Compilation.Util
import Test.Hspec

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Compilation Experiment" $ do
  -- let options = defaultOptions {optUseUIntUnionFind = True, optUseNewLinker = False}
  let options = defaultOptions {optUseUIntUnionFind = True, optUseNewLinker = True}

  describe "DivMod" $ do
    it "constant dividend / constant divisor" $ do
      let program dividend divisor = performDivMod (fromIntegral dividend) (fromIntegral divisor :: UInt 8)
      let dividend = 124
      let divisor = 36
      let expected = [dividend `div` divisor, dividend `mod` divisor]
      testCompilerWithOpts options (Prime 17) (program dividend divisor) [] [] expected
