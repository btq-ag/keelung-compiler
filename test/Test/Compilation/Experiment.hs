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
  describe "UInt constant multiplication" $ do
    let program = do
          -- 1 = out * x (mod 3)
          --
          --    * in * out = n3 + 1
          --    * n ≤ 3
          x <- input Public :: Comp (UInt 8)
          return (modInv x 3)
    it "equals zero" $ do
      debug gf181 program

-- (mod 13) 1 * 1 = 13 * 1 + 1, 2 * 7 = 13 * 1 + 1, 3 * 9 = 13 * 2 + 1, 4 * 10 = 13 * 3 + 1, 5 * 8 = 13 * 3 + 1, 6 * 11 = 13 * 5 + 1, 7 * 2 = 13 * 1 + 1, 8 * 5 = 13 * 3 + 1, 9 * 3 = 13 * 2 + 1, 10 * 4 = 13 * 3 + 1, 11 * 6 = 13 * 5 + 1, 12 * 12 = 13 * 11 + 1