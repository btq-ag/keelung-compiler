{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment where

import Keelung
import Test.Compilation.Util
import Test.Hspec

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Experiment" $ do
  it "variable dividend / constant divisor" $ do
    let program divisor = do
          dividend <- input Public :: Comp (UInt 8)
          performDivMod dividend divisor
    let dividend = 50 :: Integer
    let divisor = 1
    let expected = [dividend `div` divisor, dividend `mod` divisor]
    debug (Prime 17) (program (fromInteger divisor))
    testCompiler (Prime 17) (program (fromIntegral divisor)) [dividend] [] expected
  