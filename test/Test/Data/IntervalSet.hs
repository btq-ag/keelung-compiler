{-# LANGUAGE DataKinds #-}

module Test.Data.IntervalSet (tests, run) where

import Control.Monad (foldM, forM_)
import Data.Field.Galois (Prime)
import Keelung.Data.IntervalSet (IntervalSet)
import Keelung.Data.IntervalSet qualified as IntervalSet
import Keelung.Data.IntervalTable qualified as IntervalTable
import Test.Arbitrary ()
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Interval Sets" $ do
  describe "insert" $ do
    it "should preserve invariants after applying randomized insertions" $ do
      property testInsertion

    it "should handle cases like these" $ do
      testInsertion [Insert (24, 28) (-24), Insert (24, 29) 24, Insert (23, 27) (-65)]
      testInsertion [Insert (10, 40) 10, Insert (0, 30) 100, Insert (10, 20) (-10)]

      --    ├─  20 ─┼─  30 ─┼─  20 ─┤
      --            ├─ -10 ─┤
      testInsertion [Insert (10, 20) (-10), Insert (10, 20) 10, Insert (0, 30) 20]
      --    ├─  10 ─┤
      --            ├─  20 ─┤
      --            ├─ -20 ─┤
      testInsertion [Insert (10, 20) (-20), Insert (10, 20) 20, Insert (0, 10) 10]
      --    ├─  10 ─┤
      --            ├─  20 ─┤
      --            ├─ -10 ─┤
      testInsertion [Insert (10, 20) (-10), Insert (10, 20) 20, Insert (0, 10) 10]
      --    ├─  10 ─┼─  20 ─┼─  30 ─┤
      --            ├─ -10 ─┤
      testInsertion [Insert (10, 20) (-10), Insert (20, 30) 30, Insert (10, 20) 20, Insert (0, 10) 10]

  describe "merge" $ do
    -- it "should result in a valid IntervalSet" $ do
    --   property testMerging

    it "1" $ do
      --  ys       ├ -10 ┤
      --  xs ├  30 ┤  40 ┤  30 ┤
      testMerging ([Insert (10, 20) (-10)], [Insert (10, 20) 10, Insert (0, 30) 30])

    -- it "LT LT LT" $ do
    --   --    ├───┤
    --   --             ├───┤
    --   testMerging ([Insert (0, 10) 10], [Insert (20, 30) 10])

    -- it "LT LT EQ nil" $ do
    --   --    ├───┤
    --   --        ├───┤
    --   testMerging ([Insert (0, 10) 10], [Insert (10, 20) 10])

    -- it "LT LT EQ adjc" $ do
    --   --  xs  ├─3─┼─2────┤
    --   --  ys      ├─1─┤
    --   testMerging ([Insert (10, 30) 20, Insert (0, 10) 30], [Insert (10, 20) 10])

    -- it "LT LT EQ disj" $ do
    --   --  xs  ├─3─┤   ├───────┤
    --   --  ys      ├─1─────┤
    --   testMerging ([Insert (20, 40) 20, Insert (0, 10) 30], [Insert (10, 30) 30])

    -- it "LT LT GT" $ do
    --   --    ├───────┤
    --   --        ├────────┤
    --   testMerging ([Insert (0, 20) 10], [Insert (10, 30) (-10)])

    -- it "LT EQ" $ do
    --   --  xs  ├───────┤
    --   --  ys      ├───┤
    --   testMerging ([Insert (0, 20) 10], [Insert (10, 20) (-10)])

    -- it "LT GT" $ do
    --   --  xs  ├───────────┤
    --   --  ys      ├───┤
    --   testMerging ([Insert (0, 30) 10], [Insert (10, 20) (-10)])
    -- it "EQ LT" $ do
    --   --  xs  ├───┤
    --   --  ys  ├───────┤
    --   testMerging ([Insert (0, 10) 10], [Insert (0, 20) (-10)])

    it "EQ EQ nil nil" $ do
      --  xs  ├───┤
      --  ys  ├───┤
      testMerging ([Insert (0, 10) 10], [Insert (0, 10) (-10)])

    it "EQ EQ nil adjc" $ do
      --  xs  ├───┤
      --  ys  ├───┼───┤
      testMerging ([Insert (0, 10) 10], [Insert (0, 10) 20, Insert (10, 20) 40])
      testMerging ([Insert (0, 10) 10], [Insert (0, 10) (-10), Insert (10, 20) 30]) -- negating
      testMerging ([Insert (0, 10) 10], [Insert (0, 10) 20, Insert (10, 20) 30]) -- merging
    it "EQ EQ nil disj" $ do
      --  xs  ├───┤
      --  ys  ├───┤    ├───┤
      testMerging ([Insert (0, 10) 10], [Insert (0, 10) 20, Insert (20, 30) 40])
    -- testMerging ([Insert (0, 10) 10], [Insert (0, 10) (-10), Insert (20, 30) 40]) -- negating
    it "EQ EQ adjc adjc" $ do
      --  xs  ├───┼──..
      --  ys  ├───┼──..
      testMerging ([Insert (0, 10) 10, Insert (10, 20) 20], [Insert (0, 10) 40, Insert (10, 20) 80])
      testMerging ([Insert (0, 10) 10, Insert (10, 20) 20], [Insert (0, 10) (-10), Insert (10, 20) 80]) -- negating
      testMerging ([Insert (0, 10) 10, Insert (10, 20) 20], [Insert (0, 10) 40, Insert (10, 20) (-20)]) -- negating
      testMerging ([Insert (0, 10) 10, Insert (10, 20) 20], [Insert (0, 10) 40, Insert (10, 20) 30]) -- merging
    it "EQ EQ adjc disj" $ do
      --  xs  ├───┼──..
      --  ys  ├───┤   ├──..
      testMerging ([Insert (0, 10) 10, Insert (10, 20) 20], [Insert (0, 10) 40, Insert (20, 30) 80])
      testMerging ([Insert (0, 10) 10, Insert (10, 20) 20], [Insert (0, 10) (-10), Insert (20, 30) 80]) -- negating
      testMerging ([Insert (0, 10) 10, Insert (10, 20) 20], [Insert (0, 10) 10, Insert (20, 30) 80]) -- merging
    it "EQ EQ disj adjc" $ do
      --  xs  ├───┤   ├──..
      --  ys  ├───┼──..
      testMerging ([Insert (0, 10) 10, Insert (20, 30) 20], [Insert (0, 10) 40, Insert (10, 20) 80])
      testMerging ([Insert (0, 10) 10, Insert (20, 30) 20], [Insert (0, 10) (-10), Insert (10, 20) 80]) -- negating
      testMerging ([Insert (0, 10) 10, Insert (20, 30) 20], [Insert (0, 10) 10, Insert (10, 20) 80]) -- merging
    it "EQ EQ disj disj" $ do
      --  xs  ├───┤   ├──..
      --  ys  ├───┤   ├──..
      testMerging ([Insert (0, 10) 10, Insert (20, 30) 20], [Insert (0, 10) 40, Insert (20, 30) 80])
      testMerging ([Insert (0, 10) 10, Insert (20, 30) 20], [Insert (0, 10) (-10), Insert (20, 30) 80]) -- negating
      testMerging ([Insert (0, 10) 10, Insert (20, 30) 20], [Insert (0, 10) 10, Insert (20, 30) (-20)]) -- negating

-- it "EQ GT" $ do
--   --  xs  ├───────┤
--   --  ys  ├───┤
--   testMerging ([Insert (0, 20) 10], [Insert (0, 10) (-10)])
-- it "GT LT" $ do
--   --  xs      ├───┤
--   --  ys  ├───────────┤
--   testMerging ([Insert (10, 20) 10], [Insert (0, 30) (-10)])
-- it "GT EQ" $ do
--   --  xs      ├───┤
--   --  ys  ├───────┤
--   testMerging ([Insert (10, 20) 10], [Insert (0, 20) (-10)])
-- it "GT GT LT" $ do
--   --  xs          ├───┤
--   --  ys  ├───┤
--   testMerging ([Insert (20, 30) 10], [Insert (0, 10) 10])
--

-- it "GT GT EQ nil" $ do
--   --  xs      ├───┤
--   --  ys  ├───┤
--   testMerging ([Insert (10, 20) 10], [Insert (0, 10) 10])
-- --
-- it "GT GT EQ adjc LT negating" $ do
--   --  xs      ├───┤
--   --  ys  ├───┼───────┤
--   testMerging ([Insert (10, 20) 10], [Insert (0, 10) 20, Insert (10, 30) (-10)])

-- it "GT GT EQ adjc EQ negating" $ do
--   --  xs      ├───┤
--   --  ys  ├───┼───┤
--   testMerging ([Insert (10, 20) 10], [Insert (0, 10) 20, Insert (10, 20) (-10)])

-- it "GT GT EQ adjc GT negating" $ do
--   --  xs      ├───────┤
--   --  ys  ├───┼───┤
--   testMerging ([Insert (10, 30) 10], [Insert (0, 10) 20, Insert (10, 20) (-10)])

-- it "GT GT EQ adjc LT merging" $ do
--   --  xs      ├───┤
--   --  ys  ├───┼───────┤
--   testMerging ([Insert (10, 20) 10], [Insert (0, 10) 20, Insert (10, 30) 10])

-- it "GT GT EQ adjc EQ merging" $ do
--   --  xs      ├───┤
--   --  ys  ├───┼───┤
--   testMerging ([Insert (10, 20) 10], [Insert (0, 10) 20, Insert (10, 20) 10])

-- it "GT GT EQ adjc GT merging" $ do
--   --  xs      ├───────┤
--   --  ys  ├───┼───┤
--   testMerging ([Insert (10, 30) 10], [Insert (0, 10) 20, Insert (10, 20) 10])

-- it "GT GT EQ disj LT" $ do
--   --  xs      ├───┤
--   --  ys  ├───┤       ├───┤
--   testMerging ([Insert (10, 20) 10], [Insert (0, 10) 20, Insert (30, 40) 40])

-- it "GT GT EQ disj EQ" $ do
--   --  xs      ├───┤
--   --  ys  ├───┤   ├───┤
--   testMerging ([Insert (10, 20) 10], [Insert (0, 10) 20, Insert (20, 30) 40])

-- it "GT GT EQ disj GT" $ do
--   --  xs      ├───────┤
--   --  ys  ├───┤   ├───┤
--   testMerging ([Insert (10, 30) 10], [Insert (0, 10) 20, Insert (20, 30) 40])

-- it "GT GT GT nil" $ do
--   --  xs      ├───────┤
--   --  ys  ├───────┤
--   testMerging ([Insert (10, 30) 10], [Insert (0, 20) (-10)])

-- it "GT GT GT adjc negating LT" $ do
--   --  xs      ├───────┤
--   --  ys  ├───────┼───────┤
--   testMerging ([Insert (10, 30) 10], [Insert (0, 20) (-10), Insert (20, 40) 10])

-- it "GT GT GT adjc negating EQ" $ do
--   --  xs      ├───────┤
--   --  ys  ├───────┼───┤
--   testMerging ([Insert (10, 30) 10], [Insert (0, 20) (-10), Insert (20, 30) 10])

-- it "GT GT GT adjc negating GT" $ do
--   --  xs      ├───────────┤
--   --  ys  ├───────┼───┤
--   testMerging ([Insert (10, 40) 10], [Insert (0, 20) (-10), Insert (20, 30) 10])

-- it "GT GT GT disc" $ do
--   --  xs      ├───────────┤
--   --  ys  ├───────┤   ├───┤
--   testMerging ([Insert (10, 40) 10], [Insert (0, 20) (-10), Insert (30, 40) 10])

-- describe "singleton" $ do
--   it "should result in a valid IntervalSet" $ do
--     property $ \(start, end, count) -> do
--       case IntervalSet.singleton (start, end) (count :: Prime 17) of
--         Nothing -> return ()
--         Just xs -> IntervalSet.validate xs `shouldBe` Nothing

-- describe "toIntervalTable" $ do
--   it "should generate well-behaved IntervalTable" $ do
--     property $ \(NonOverlappingOperations operations points) -> do
--       let intervals = foldr applyOperation IntervalSet.new operations
--       let table = IntervalSet.toIntervalTable 200 intervals
--       IntervalTable.size table `shouldBe` sum (map sizeOfOperation operations)
--       forM_ points $ \point -> do
--         IntervalTable.member (point, point + 1) table `shouldBe` memberOfNonOverlappingOperations (NonOverlappingOperations operations points) point

-- describe "intervalsWithin" $ do
--   it "should result in correct intervals" $ do
--     property $ \(operations, Interval interval) -> do
--       let xs = foldr applyOperation IntervalSet.new (operations :: [Operation Int])
--       let intervals = IntervalSet.intervalsWithin xs interval
--       let withinIntervals x = any (\(start, end) -> x >= start && x < end) intervals
--       -- all points within the computed intervals should be members of the interval set
--       forM_ [fst interval .. snd interval - 1] $ \point -> do
--         let expected = IntervalSet.member xs point
--         let actual = withinIntervals point
--         actual `shouldBe` expected

-- describe "split" $ do
--   it "should be the inverse of merge after nomalization" $ do
--     property $ \(xs, i) -> do
--       let (as, bs) = IntervalSet.split xs i
--       let expected = xs :: IntervalSet Int
--       let actual = IntervalSet.normalize (as <> bs)
--       actual `shouldBe` expected
--       IntervalSet.validate actual `shouldBe` Nothing

--------------------------------------------------------------------------------

instance (Arbitrary n, Eq n, Num n, Show n) => Arbitrary (IntervalSet n) where
  arbitrary = do
    -- create a new IntervalSet by inserting a random number of random intervals with IntervalSet.insert
    intervals <- arbitrary :: (Arbitrary n, Num n) => Gen [(Interval, n)]
    pure $ foldl (\xs (Interval interval, count) -> IntervalSet.normalize $ IntervalSet.insert interval count xs) IntervalSet.new intervals

--------------------------------------------------------------------------------

newtype Interval = Interval (Int, Int) deriving (Eq, Show)

instance Arbitrary Interval where
  arbitrary = do
    start <- chooseInt (0, 100)
    len <- chooseInt (0, 5)
    pure $ Interval (start, start + len)

--------------------------------------------------------------------------------

testInsertion :: [Operation Int] -> IO ()
testInsertion operations = do
  let intervals = foldr (\(Insert interval n) -> IntervalSet.insert interval n) IntervalSet.new operations
  IntervalSet.totalCount intervals `shouldBe` sum (map countOfOperation operations)
  IntervalSet.validate intervals `shouldBe` Nothing

testMerging :: ([Operation Int], [Operation Int]) -> IO ()
testMerging (xs, ys) = do
  let x = foldr applyOperation IntervalSet.new xs
  let y = foldr applyOperation IntervalSet.new ys
  let result = x <> y
  IntervalSet.totalCount result `shouldBe` IntervalSet.totalCount x + IntervalSet.totalCount y
  IntervalSet.validate result `shouldBe` Nothing

--------------------------------------------------------------------------------

-- | Datatype for testing operations on interval sets
data Operation n = Insert (Int, Int) n deriving (Eq, Show)

-- | Generate a random operation
instance (Num n) => Arbitrary (Operation n) where
  arbitrary = do
    Interval interval <- arbitrary
    amount <- chooseInt (-100, 100)
    pure $ Insert interval (fromIntegral amount)

-- | Apply an operation to an interval set
applyOperation :: (Num n, Eq n) => Operation n -> IntervalSet n -> IntervalSet n
applyOperation (Insert interval amount) = IntervalSet.insert interval amount

-- | Calculate the total count of an operation
countOfOperation :: (Num n) => Operation n -> n
countOfOperation (Insert (start, end) amount) = amount * fromIntegral (end - start)

-- | Calculate the total size of an operation
sizeOfOperation :: (Eq n, Num n) => Operation n -> Int
sizeOfOperation (Insert (start, end) amount) = if amount == 0 then 0 else end - start

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
              x@(Insert (_, end) _) <- genOperation start
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
        pure (Insert (start, end) (fromIntegral amount))

memberOfNonOverlappingOperations :: (Eq n, Num n) => NonOverlappingOperations n -> Int -> Bool
memberOfNonOverlappingOperations (NonOverlappingOperations operations _) point =
  any (\(Insert (start, end) amount) -> amount /= 0 && start <= point && point < end) operations