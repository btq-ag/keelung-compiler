module Test.Optimization.Field (tests, run) where

import Keelung
import Test.Util
import Test.Hspec

tests :: SpecWith ()
tests = do
  describe "Field" $ do
    -- 1
    it "x `pow` 0" $ do
      let program = do
            x <- inputField Public
            return $ x `pow` 0
      assertCountO0 gf181 program 1
      assertCount gf181 program 1

    -- ((x ^ 2) ^ 2) * x
    it "x `pow` 5" $ do
      let program = do
            x <- inputField Public
            return $ x `pow` 5
      assertCountO0 gf181 program 5
      assertCount gf181 program 3

    -- ((((x ^ 2) * x) ^ 2) ^ 2) * x
    it "x `pow` 13" $ do
      let program = do
            x <- inputField Public
            return $ x `pow` 13
      assertCountO0 gf181 program 7
      assertCount gf181 program 5

--------------------------------------------------------------------------------

run :: IO ()
run = hspec tests
