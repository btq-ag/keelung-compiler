{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment (run, tests) where

import Keelung
import Test.Arbitrary ()
import Test.Compilation.Util
import Test.Hspec

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "DivMod" $ do
    it "variable dividend / constant divisor" $ do
      let program divisor = do
            dividend <- input Public :: Comp (UInt 8)
            performDivMod dividend divisor
      let dividend = 239
      let divisor = 20
      let expected = [dividend `div` divisor, dividend `mod` divisor]
      debug (Prime 17) (program (fromIntegral divisor)) 
      testCompiler (Prime 17) (program (fromIntegral divisor)) [dividend] [] expected
      -- debugSolver (Prime 17) (program (fromIntegral divisor)) [dividend] []
