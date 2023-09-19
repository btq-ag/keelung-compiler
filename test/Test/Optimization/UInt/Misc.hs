{-# LANGUAGE DataKinds #-}

module Test.Optimization.UInt.Misc (tests, run) where

import Keelung
import Test.Hspec
import Test.Optimization.Util

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Misc" $ do
  describe "Carry-less Multiplication" $ do
    it "2 byte variables" $ do
      -- constraint breakdown:
      -- I/O: 24 = 2 * 8 + 8
      -- ANDs: 36 = 8 * 9 / 2
      -- XORs: 7
      (cs, cs') <- executeGF181 $ do
        x <- input Public :: Comp (UInt 8)
        y <- input Public :: Comp (UInt 8)
        return (x .*. y)
      cs `shouldHaveSize` 75
      cs' `shouldHaveSize` 67