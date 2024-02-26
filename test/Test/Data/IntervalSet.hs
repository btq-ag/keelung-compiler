{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Test.Data.IntervalSet (tests, run) where

import Control.Monad (foldM, forM_)
import Keelung.Data.IntervalSet (IntervalSet)
import Keelung.Data.IntervalSet qualified as IntervalSet
import Keelung.Data.IntervalTable qualified as IntervalTable
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Interval Sets" $ do
  describe "adjust" $ do
    it "should merge adjecent intervals with the count" $ do
      let operations = [Adjust (0, 10) 1, Adjust (10, 20) 1]
      let intervals = foldr applyOperation IntervalSet.new (operations :: [Operation Int])
      IntervalSet.totalCount intervals `shouldBe` sum (map countOfOperation operations)
      IntervalSet.validate intervals `shouldBe` Nothing

    it "should merge adjecent intervals with the count" $ do
      let operations = [Adjust (10, 20) 1, Adjust (0, 10) 1]
      let intervals = foldr applyOperation IntervalSet.new (operations :: [Operation Int])
      IntervalSet.totalCount intervals `shouldBe` sum (map countOfOperation operations)
      IntervalSet.validate intervals `shouldBe` Nothing

    it "should merge adjecent intervals with the count" $ do
      let operations = [Adjust (10, 20) 10, Adjust (0, 30) (-5), Adjust (20, 30) 10]
      let intervals = foldr applyOperation IntervalSet.new (operations :: [Operation Int])
      IntervalSet.totalCount intervals `shouldBe` sum (map countOfOperation operations)
      IntervalSet.validate intervals `shouldBe` Nothing

    it "should merge adjecent intervals with the count" $ do
      let operations = [Adjust (40, 60) 10, Adjust (60, 100) 30, Adjust (50, 60) 20]
      let intervals = foldr applyOperation IntervalSet.new (operations :: [Operation Int])
      IntervalSet.totalCount intervals `shouldBe` sum (map countOfOperation operations)
      IntervalSet.validate intervals `shouldBe` Nothing

    it "should merge adjecent intervals with the count" $ do
      let operations = [Adjust (20, 30) 20, Adjust (0, 20) 20, Adjust (10, 40) 40]
      -- 20 60 60 40
      let intervals = foldr applyOperation IntervalSet.new (operations :: [Operation Int])
      IntervalSet.totalCount intervals `shouldBe` sum (map countOfOperation operations)
      IntervalSet.validate intervals `shouldBe` Nothing

    it "should preserve invariants after applying randomized adjustments" $ do
      property $ \operations -> do
        let intervals = foldr applyOperation IntervalSet.new (operations :: [Operation Int])
        IntervalSet.totalCount intervals `shouldBe` sum (map countOfOperation operations)
        IntervalSet.validate intervals `shouldBe` Nothing

  describe "toIntervalTable" $ do
    it "should generate well-behaved IntervalTable" $ do
      property $ \(NonOverlappingOperations operations points) -> do
        let intervals = foldr applyOperation IntervalSet.new operations
        let table = IntervalSet.toIntervalTable 200 intervals
        IntervalTable.size table `shouldBe` sum (map sizeOfOperation operations)
        forM_ points $ \point -> do
          IntervalTable.member (point, point + 1) table `shouldBe` memberOfNonOverlappingOperations (NonOverlappingOperations operations points) point

  describe "intervalsWithin" $ do
    it "should result in correct intervals" $ do
      property $ \(operations, Interval interval) -> do
        let xs = foldr applyOperation IntervalSet.new (operations :: [Operation Int])
        let intervals = IntervalSet.intervalsWithin xs interval
        let withinIntervals x = any (\(start, end) -> x >= start && x < end) intervals
        -- all points within the computed intervals should be members of the interval set
        forM_ [fst interval .. snd interval - 1] $ \point -> do
          let expected = IntervalSet.member xs point
          let actual = withinIntervals point
          actual `shouldBe` expected

  describe "split" $ do
    it "should be the inverse of merge after nomalization" $ do
      property $ \(xs, i) -> do
        let (as, bs) = IntervalSet.split xs i
        let expected = xs :: IntervalSet Int
        let actual = IntervalSet.normalize (as <> bs)
        actual `shouldBe` expected
        IntervalSet.validate actual `shouldBe` Nothing

--------------------------------------------------------------------------------

instance (Arbitrary n, Eq n, Num n, Show n) => Arbitrary (IntervalSet n) where
  arbitrary = do
    -- create a new IntervalSet by inserting a random number of random intervals with IntervalSet.adjust
    intervals <- arbitrary :: (Arbitrary n, Num n) => Gen [(Interval, n)]
    pure $ foldl (\xs (Interval interval, count) -> IntervalSet.normalize $ IntervalSet.adjust interval count xs) IntervalSet.new intervals

--------------------------------------------------------------------------------

newtype Interval = Interval (Int, Int) deriving (Eq, Show)

instance Arbitrary Interval where
  arbitrary = do
    start <- chooseInt (0, 100)
    len <- chooseInt (0, 5)
    pure $ Interval (start, start + len)

--------------------------------------------------------------------------------

-- | Datatype for testing operations on interval sets
data Operation n = Adjust (Int, Int) n deriving (Eq, Show)

-- | Generate a random operation
instance (Num n) => Arbitrary (Operation n) where
  arbitrary = do
    Interval interval <- arbitrary
    amount <- chooseInt (-100, 100)
    pure $ Adjust interval (fromIntegral amount)

-- | Apply an operation to an interval set
applyOperation :: (Num n, Eq n) => Operation n -> IntervalSet n -> IntervalSet n
applyOperation (Adjust interval amount) = IntervalSet.adjust interval amount

-- | Calculate the total count of an operation
countOfOperation :: (Num n) => Operation n -> n
countOfOperation (Adjust (start, end) amount) = amount * fromIntegral (end - start)

-- | Calculate the total size of an operation
sizeOfOperation :: (Eq n, Num n) => Operation n -> Int
sizeOfOperation (Adjust (start, end) amount) = if amount == 0 then 0 else end - start

--------------------------------------------------------------------------------

-- | Datatype for testing operations on non-overlapping interval sets
data NonOverlappingOperations n = NonOverlappingOperations [Operation n] [Int] deriving (Eq, Show)

-- | Generate a random operation
instance (Num n) => Arbitrary (NonOverlappingOperations n) where
  arbitrary = do
    numberOfEntries <- chooseInt (0, 20)
    entries <-
      fst
        <$> foldM
          ( \(acc, prevEnd) _ -> do
              gap <- chooseInt (0, 4)
              let start = prevEnd + gap
              x@(Adjust (_, end) _) <- genOperation start
              return (x : acc, end)
          )
          ([], 0)
          [1 .. numberOfEntries]

    points <- listOf $ chooseInt (0, 100)

    return $ NonOverlappingOperations entries points
    where
      genOperation start = do
        len <- chooseInt (0, 10)
        let end = start + len
        amount <- chooseInt (0, 10)
        pure (Adjust (start, end) (fromIntegral amount))

memberOfNonOverlappingOperations :: (Eq n, Num n) => NonOverlappingOperations n -> Int -> Bool
memberOfNonOverlappingOperations (NonOverlappingOperations operations _) point =
  any (\(Adjust (start, end) amount) -> amount /= 0 && start <= point && point < end) operations