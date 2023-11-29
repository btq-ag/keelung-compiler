{-# LANGUAGE DataKinds #-}

module Test.Data.IntervalTree (tests, run) where

import Keelung.Data.IntervalTree (IntervalTree)
import Keelung.Data.IntervalTree qualified as IntervalTree
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Interval Tree" $ do
  describe "insert" $ do
    it "randomized" $ do
      property $ \operations -> do
        let tree = foldr applyOperation IntervalTree.new operations
        IntervalTree.totalCount tree `shouldBe` sum (map countOperation operations)

--------------------------------------------------------------------------------

-- | Datatype for testing operations on interval trees
data Operation = Increase (Int, Int) Int deriving (Eq, Show)

-- | Generate a random operation
instance Arbitrary Operation where
  arbitrary = do
    start <- chooseInt (0, 100)
    len <- chooseInt (0, 100)
    let end = start + len
    amount <- chooseInt (0, 100)
    pure $ Increase (start, end) amount

-- | Apply an operation to an interval tree
applyOperation :: Operation -> IntervalTree -> IntervalTree
applyOperation (Increase interval amount) = IntervalTree.increase interval amount

-- | Calculate the total count of an operation
countOperation :: Operation -> Int
countOperation (Increase (start, end) amount) = amount * (end - start)
