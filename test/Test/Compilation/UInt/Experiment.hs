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
  -- let options = defaultOptions {optUseNewLinker = False, optOptimize = False}
  -- let options = defaultOptions {optUseNewLinker = False}
  let options = defaultOptions {optUseNewLinker = True}
  -- let options = defaultOptions {optUseNewLinker = True, optOptimize = False}

  describe "DivMod" $ do
    it "constant dividend / constant divisor" $ do
      let program dividend divisor = performDivMod (fromIntegral dividend) (fromIntegral divisor :: UInt 4)
      let dividend = 12 :: Integer
      let divisor = 5 :: Integer
      let expected = [dividend `div` divisor, dividend `mod` divisor]
      -- debugWithOpts options (Binary 7) (program dividend divisor)
      -- testCompilerWithOpts options (Binary 7) (program dividend divisor) [] [] expected
      debugWithOpts options (Binary 7) (program dividend divisor)
      testCompilerWithOpts options (Binary 7) (program dividend divisor) [] [] expected

  -- -- WON'T FIX: for the old linker
  -- describe "Binary Addition" $ do
  --   it "mixed (positive / negative / constnat) / Byte" $ do
  --     let program = do
  --           x <- input Public :: Comp (UInt 2)
  --           y <- input Public
  --           z <- input Public
  --           return $ 1 + x + y + z
  --     debug (Binary 7) program
  --     testCompiler (Binary 7) program [0, 0, 1] [] [2]