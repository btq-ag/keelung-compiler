{-# LANGUAGE DataKinds #-}

module Test.Data.IntervalSet (tests, run) where

import Keelung.Data.IntervalSet (IntervalSet)
import Keelung.Data.IntervalSet qualified as IntervalSet
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Interval Sets" $ do
  describe "IntervalSet.adjust" $ do
    it "should preserve invariants after applying randomized adjustments" $ do
      property $ \operations -> do
        let intervals = foldr applyOperation IntervalSet.new operations
        IntervalSet.count intervals `shouldBe` sum (map countOfOperation operations)
        IntervalSet.isValid intervals `shouldBe` True

--------------------------------------------------------------------------------

-- | Datatype for testing operations on interval sets
data Operation = Adjust (Int, Int) Int deriving (Eq, Show)

-- | Generate a random operation
instance Arbitrary Operation where
  arbitrary = do
    start <- chooseInt (0, 100)
    len <- chooseInt (0, 100)
    let end = start + len
    amount <- chooseInt (-100, 100)
    pure $ Adjust (start, end) amount

-- | Apply an operation to an interval set
applyOperation :: Operation -> IntervalSet -> IntervalSet
applyOperation (Adjust interval amount) = IntervalSet.adjust interval amount

-- | Calculate the total count of an operation
countOfOperation :: Operation -> Int
countOfOperation (Adjust (start, end) amount) = amount * (end - start)