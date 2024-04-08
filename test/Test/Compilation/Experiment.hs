{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment (run, tests) where

import Data.Bits qualified
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
    it "from variables" $ do
      let program = do
            xs <- inputList Public 8
            fromBools xs :: Comp (UInt 8)
      let x = 1 :: Int
      let bits = map (\b -> if b then 1 else 0) $ Data.Bits.testBit x <$> [0 .. 7]
      -- forM_ [gf181, Prime 2, Binary 7] $ \field -> do
      testCompiler (Binary 7) program bits [] [fromIntegral x]
      testCompiler (Prime 2) program bits [] [fromIntegral x]
      testCompiler gf181 program bits [] [fromIntegral x]