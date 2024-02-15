{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Experiment (tests, run) where

import Keelung hiding (compile)
-- import Keelung.Compiler.Options
import Test.Compilation.Util
import Test.Hspec

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Compilation Experiment" $ do
  -- let options = defaultOptions {optUseNewLinker = False}
  -- let options = defaultOptions {optUseNewLinker = True}
  -- let options = defaultOptions {optUseNewLinker = True, optOptimize = False}

  describe "DivMod" $ do
    --   it "constant dividend / constant divisor" $ do
    --     let program dividend divisor = performDivMod (fromIntegral dividend) (fromIntegral divisor :: UInt 4)
    --     let dividend = 12
    --     let divisor = 5
    --     let expected = [dividend `div` divisor, dividend `mod` divisor]
    --     debugWithOpts options (Binary 7) (program dividend divisor)
    --     testCompilerWithOpts options (Binary 7) (program dividend divisor) [] [] expected

    it "2 negative variables / UInt 2" $ do
      let program = do
            x <- input Public :: Comp (UInt 2)
            y <- input Public
            return $ -x - y
      let x = 2
      let y = 1
      let expected = [toInteger (-x - y) `mod` 4]
      debug (Binary 7) program
      testCompiler (Binary 7) program [x, y] [] expected
