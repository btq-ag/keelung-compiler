{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Experiment (tests, run) where

import Keelung hiding (compile)
import Keelung.Compiler.Options
import Keelung.Data.U qualified as U
import Test.Compilation.Util
import Test.Hspec

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Compilation Experiment" $ do
  -- let options = defaultOptions {optUseUIntUnionFind = True, optUseNewLinker = False, optOptimize = False}
  let options = defaultOptions {optUseUIntUnionFind = True, optUseNewLinker = True}
  -- let options = defaultOptions {optUseUIntUnionFind = True, optUseNewLinker = True, optOptimize = False}
  describe "Addition" $ do
    it "1 variable / 1 constant" $ do
      let program y = do
            x <- input Public
            return (x .*. fromInteger y :: UInt 8)
      let x = 0
      let y = 0
      let expected = [U.uValue (U.clMul (U.new 8 (toInteger x)) (U.new 8 (toInteger y)))]
      debugWithOpts options gf181 (program y)
      testCompilerWithOpts options gf181 (program y) [x] [] expected

-- describe "DivMod" $ do
--   it "constant dividend / constant divisor" $ do
--     let program dividend divisor = performDivMod (fromIntegral dividend) (fromIntegral divisor :: UInt 8)
--     -- let genPair = do
--     --       dividend <- choose (0, 255)
--     --       divisor <- choose (1, 255)
--     --       return (dividend, divisor)
--     -- forAll genPair $ \(dividend, divisor) -> do
--     let dividend = 3
--         divisor = 20
--     let expected = [dividend `div` divisor, dividend `mod` divisor]
--     forM_ [Prime 17] $ \field -> do
--       debugWithOpts options field (program dividend divisor)
--       testCompilerWithOpts options field (program dividend divisor) [] [] expected