{-# LANGUAGE DataKinds #-}

module Test.Data.IntervalTree (tests, run) where

import Keelung.Data.IntervalTree qualified as IntervalTree
import Test.Hspec

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Interval Tree" $ do
  describe "insert" $ do
    it "simple" $ do
      let tree1 = IntervalTree.increase (10, 12) 6 IntervalTree.new
      IntervalTree.tally tree1 `shouldBe` 12
      let tree2 = IntervalTree.increase (12, 15) 4 tree1
      IntervalTree.tally tree2 `shouldBe` 24
      let tree3 = IntervalTree.increase (11, 15) 4 tree2
      print $ IntervalTree.expose tree3
      IntervalTree.tally tree3 `shouldBe` 40
