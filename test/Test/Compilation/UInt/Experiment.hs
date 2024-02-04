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
  let options = defaultOptions {optUseUIntUnionFind = True, optUseNewLinker = True}

  describe "Multiplication" $ do
    it "2 variables / 1 constant" $ do
      let program c = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public
            return $ x .*. y .*. fromInteger c
      -- debugWithOpts options gf181 (program 0)
      testCompilerWithOpts options gf181 (program 0) [0, 0] [] [0]

-- describe "Binary field" $ do
--   it "variable dividend / variable divisor" $ do
--       let program = do
--             dividend <- input Public :: Comp (UInt 4)
--             divisor <- input Public
--             performDivMod dividend divisor

--       -- let genPair = do
--       --       dividend <- choose (0, 255)
--       --       divisor <- choose (1, 255)
--       --       return (dividend, divisor)

--       -- forAll genPair $ \(dividend, divisor) -> do
--       --   let expected = [dividend `div` divisor, dividend `mod` divisor]
--       --   testCompilerWithOpts options gf181 program [dividend, divisor] [] expected
--         -- testCompilerWithOpts options (Prime 17) program [dividend, divisor] [] expected
--         -- testCompilerWithOpts options (Binary 7) program [dividend, divisor] [] expected

--       let dividend = 10
--       let divisor = 3
--       let expected = [dividend `div` divisor, dividend `mod` divisor]
--       -- debugWithOpts options gf181 program
--       testCompilerWithOpts options gf181 program [dividend, divisor] [] expected
--       -- debugSolverWithOpts options gf181 program [dividend, divisor] []
