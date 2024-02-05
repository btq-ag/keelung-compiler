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
  -- let options = defaultOptions {optUseUIntUnionFind = True, optUseNewLinker = True}
  let options = defaultOptions {optUseUIntUnionFind = True, optUseNewLinker = True, optOptimize = False}

  describe "DivMod" $ do
    -- it "constant dividend / constant divisor" $ do
    --   let program dividend divisor = performDivMod (fromIntegral dividend) (fromIntegral divisor :: UInt 4)
    --   let dividend = 12
    --   let divisor = 5
    --   let expected = [dividend `div` divisor, dividend `mod` divisor]
    --   debugWithOpts options (Binary 7) (program dividend divisor)
    --   testCompilerWithOpts options (Binary 7) (program dividend divisor) [] [] expected

    it "1 negative variable + 1 constant / Byte" $ do
      let program y = do
            x <- input Public :: Comp (UInt 2)
            return $ y - x
      debugWithOpts options (Binary 7) (program 3)
      testCompilerWithOpts options (Binary 7) (program 3) [0] [] [3]

      -- let program y = do
      --       x <- input Public :: Comp (UInt 4)
      --       return $ -x + y
      -- debugWithOpts options (Binary 7) (program 3)
      -- testCompilerWithOpts options (Binary 7) (program 3) [0] [] [3]
