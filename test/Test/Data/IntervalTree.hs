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
  describe "IntervalTree.adjust" $ do
    it "should preserve invariants after applying randomized adjustments" $ do
      property $ \operations -> do
        let tree = foldr applyOperation IntervalTree.new operations
        IntervalTree.totalCount tree `shouldBe` sum (map countOperation operations)
        IntervalTree.isValid tree `shouldBe` True

--------------------------------------------------------------------------------

-- | Datatype for testing operations on interval trees
data Operation = Adjust (Int, Int) Int deriving (Eq, Show)

-- | Generate a random operation
instance Arbitrary Operation where
  arbitrary = do
    start <- chooseInt (0, 100)
    len <- chooseInt (0, 100)
    let end = start + len
    amount <- chooseInt (-100, 100)
    pure $ Adjust (start, end) amount

-- | Apply an operation to an interval tree
applyOperation :: Operation -> IntervalTree -> IntervalTree
applyOperation (Adjust interval amount) = IntervalTree.adjust interval amount

-- | Calculate the total count of an operation
countOperation :: Operation -> Int
countOperation (Adjust (start, end) amount) = amount * (end - start)
