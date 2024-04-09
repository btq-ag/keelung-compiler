{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment (run, tests) where

import Control.Monad
import Keelung
import Test.Arbitrary ()
import Test.Compilation.Util
import Test.Hspec

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

-- | Equalities:
--    introduce a new variable m
--    if input = 0 then m = 0 else m = recip input
--    Equality:
--      input * m = 1 - output
--      input * output = 0
tests :: SpecWith ()
tests = describe "Experiment" $ do
  -- describe "freshVarField" $ do
  --   it "equals zero" $ do
  --     let program = do
  --           x <- inputField Public
  --           out <- freshVarField
  --           m <- freshVarField
  --           assert $ (x * m) `eq` (1 - out)
  --           assert $ (x * out) `eq` 0
  --           return out
  --     solveOutput gf181 program [2] [] `shouldReturn` [0]
  --     solveOutput gf181 program [1] [] `shouldReturn` [0]
  --     solveOutput gf181 program [0] [] `shouldReturn` [1]

  describe "fromBools" $ do
    it "constant dividend / constant divisor" $ do
      let program dividend divisor = performDivMod (fromIntegral dividend) (fromIntegral divisor :: UInt 8)
      let dividend = 137 :: Integer
      let divisor = 2 :: Integer
      let expected = [dividend `div` divisor, dividend `mod` divisor]
      forM_ [gf181, Prime 17, Binary 7] $ \field -> do
        validate field (program dividend divisor) [] [] expected
