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
  -- let options = defaultOptions {optUseNewLinker = False}
  let options = defaultOptions {optUseNewLinker = True}

  describe "DivMod" $ do
    -- it "constant dividend / constant divisor" $ do
    --   let program dividend divisor = performDivMod (fromIntegral dividend) (fromIntegral divisor :: UInt 4)
    --   let dividend = 12
    --   let divisor = 5
    --   let expected = [dividend `div` divisor, dividend `mod` divisor]
    --   debugWithOpts options (Binary 7) (program dividend divisor)
    --   testCompilerWithOpts options (Binary 7) (program dividend divisor) [] [] expected

    it "before reuse" $ do
      let program = do
            a <- input Public :: Comp (UInt 5)
            b <- input Public
            (q, _) <- performDivMod a b
            reuse q
      testCompilerWithOpts options gf181 program [10, 4] [] [2]
