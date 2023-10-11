{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Misc (tests, run) where

import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "DivMod" $ do
    it "performDivMod (on constants) (issue #18)" $ do
      let program dividend divisor = performDivMod (fromInteger dividend) (fromInteger divisor :: UInt 4)
      -- let genPair = do
      --       dividend <- choose (0, 15)
      --       divisor <- choose (1, 15)
      --       return (dividend, divisor)
      -- forAll genPair $ \(dividend, divisor) -> do
      --   let expected = [dividend `div` divisor, dividend `mod` divisor]
      --   runAll gf181 (program dividend divisor) [] [] expected
      --   runAll (Prime 17) (program dividend divisor) [] [] expected
      let dividend = 3
      let divisor = 1
      -- let expected = [dividend `div` divisor, dividend `mod` divisor]
      -- runAll gf181 (program dividend divisor) [] [] expected
      -- runAll (Prime 17) (program dividend divisor) [] [] expected
      debugUnoptimized (Prime 17) (program dividend divisor)
      debug (Prime 17) (program dividend divisor)
