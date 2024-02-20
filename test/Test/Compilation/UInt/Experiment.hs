{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Experiment (tests, run) where

import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Compilation Experiment" $ do
  -- let options = defaultOptions {optUseNewLinker = False, optOptimize = False}
  -- let options = defaultOptions {optUseNewLinker = False}
  -- let options = defaultOptions {optUseNewLinker = True, optOptimize = False}

  describe "DivMod" $ do
    -- let expected = [dividend `div` divisor, dividend `mod` divisor]

    it "more than 4 positive variables" $ do
      let program n = do
            x <- input Public :: Comp (UInt 4)
            return $ sum (replicate (fromInteger n) x)
      let expected = [10 * 10 `mod` 16]
      debug (Prime 61) (program 10)
      testCompiler (Prime 61) (program 10) [10] [] expected

-- debugSolverWithOpts options (Binary 7) (program (fromIntegral divisor)) [dividend] []

-- debugSolverWithOpts options (Binary 7) (program dividend divisor) [] []
-- 4294967291
-- 4294967311

-- let genPair = do
--         dividend <- choose (0, 3)
--         divisor <- choose (1, 3)
--         return (dividend, divisor)
-- forAll genPair $ \(dividend, divisor) -> do
--   let expected = [dividend `div` divisor, dividend `mod` divisor]
--   -- debugWithOpts options (Binary 7) (program dividend divisor)
--   testCompilerWithOpts options (Binary 7) (program dividend divisor) [] [] expected

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