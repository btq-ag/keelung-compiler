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
    -- it "CaseL1" $ do
    --   --     A   B
    --   --     ├───┤
    --   --             ├───┤
    --   --             X   Y
    --   testInsertion [Insert (0, 10) 10, Insert (20, 30) 1]
    -- it "CaseL2" $ do
    --   --   A   B
    --   --   ├───┤
    --   --       ├───┤
    --   --       X   Y
    --   testInsertion [Insert (0, 10) 10, Insert (10, 20) 1]

    -- it "CaseL3" $ do
    --   --     A       B
    --   --     ├───────┤
    --   --         ├───────┤
    --   --         X       Y
    --   testInsertion [Insert (0, 20) 10, Insert (10, 30) 1]

    -- it "CaseL3 negating" $ do
    --   --     A       B
    --   --     ├───────┤
    --   --         ├───────┤
    --   --         X       Y
    --   testInsertion [Insert (0, 20) (-10), Insert (10, 30) 10]

    -- it "CaseL4 empty" $ do
    --   --     A       B
    --   --     ├───────┤
    --   --         ├───┤
    --   --         X   Y
    --   testInsertion [Insert (0, 20) 10, Insert (10, 20) 1]

    -- it "CaseL4 empty negating" $ do
    --   --     A       B
    --   --     ├───────┤
    --   --         ├───┤
    --   --         X   Y
    --   testInsertion [Insert (0, 20) (-10), Insert (10, 20) 10]

    -- it "CaseL4 non-immediate" $ do
    --   --     A       B
    --   --     ├───────┤
    --   --         ├───┤   ├───┤
    --   --         X   Y   Z   W
    --   testInsertion [Insert (0, 20) 10, Insert (30, 40) 2, Insert (10, 20) 1]

    -- it "CaseL4 immediate" $ do
    --   --     A       B
    --   --     ├───────┤
    --   --         ├───┼───┤
    --   --         X   Y   W
    --   testInsertion [Insert (0, 20) 10, Insert (20, 30) 2, Insert (10, 20) 1]

    -- it "CaseL4 immediate merging" $ do
    --   --     A       B
    --   --     ├───────┤
    --   --         ├───┼───┤
    --   --         X   Y   W
    --   testInsertion [Insert (0, 20) 10, Insert (20, 30) 20, Insert (10, 20) 10]

    -- it "CaseL5 empty" $ do
    --   --     A           B
    --   --     ├───────────┤
    --   --         ├───┤
    --   --         X   Y
    --   testInsertion [Insert (0, 30) 10, Insert (10, 20) 1]

    -- it "CaseL5 empty negating" $ do
    --   --     A           B
    --   --     ├───────────┤
    --   --         ├───┤
    --   --         X   Y
    --   testInsertion [Insert (0, 30) (-10), Insert (10, 20) 10]

    -- it "CaseL5 non-immediate 1" $ do
    --   --     A           B
    --   --     ├───────────┤
    --   --         ├───┤       ├───┤
    --   --         X   Y       Z   W
    --   testInsertion [Insert (0, 30) 10, Insert (40, 50) 2, Insert (10, 20) 1]

    -- it "CaseL5 non-immediate 2" $ do
    --   --     A           B
    --   --     ├───────────┤
    --   --         ├───┤   ├───┤
    --   --         X   Y   Z   W
    --   testInsertion [Insert (0, 30) 10, Insert (30, 40) 2, Insert (10, 20) 1]

    -- it "CaseL5 non-immediate 3" $ do
    --   --     A               B
    --   --     ├───────────────┤
    --   --         ├───┤   ├───────┤
    --   --         X   Y   Z       W
    --   testInsertion [Insert (0, 40) 10, Insert (30, 50) 2, Insert (10, 20) 1]

    -- it "CaseL5 non-immediate 4" $ do
    --   --     A               B
    --   --     ├───────────────┤
    --   --         ├───┤   ├───┤
    --   --         X   Y   Z   W
    --   testInsertion [Insert (0, 40) 10, Insert (30, 40) 2, Insert (10, 20) 1]

    -- it "CaseL5 non-immediate 5" $ do
    --   --     A                   B
    --   --     ├───────────────────┤
    --   --         ├───┤   ├───┤
    --   --         X   Y   Z   W
    --   testInsertion [Insert (0, 50) 10, Insert (30, 40) 2, Insert (10, 20) 1]

    -- it "CaseL5 immediate 1" $ do
    --   --     A           B
    --   --     ├───────────┤
    --   --         ├───┼───────┤
    --   --         X   Y       W
    --   testInsertion [Insert (0, 30) 10, Insert (20, 40) 2, Insert (10, 20) 1]

    -- it "CaseL5 immediate 2" $ do
    --   --     A           B
    --   --     ├───────────┤
    --   --         ├───┼───┤
    --   --         X   Y   W
    --   testInsertion [Insert (0, 30) 10, Insert (20, 30) 2, Insert (10, 20) 1]

    -- it "CaseL5 immediate 3" $ do
    --   --     A               B
    --   --     ├───────────────┤
    --   --         ├───┼───┤
    --   --         X   Y   W
    --   testInsertion [Insert (0, 40) 10, Insert (20, 30) 2, Insert (10, 20) 1]

    -- it "CaseM1" $ do
    --   --     A   B
    --   --     ├───┤
    --   --     ├───────┤
    --   --     X       Y
    --   testInsertion [Insert (0, 10) 10, Insert (0, 20) 1]

    -- it "CaseM1 negating" $ do
    --   --     A   B
    --   --     ├───┤
    --   --     ├───────┤
    --   --     X       Y
    --   testInsertion [Insert (0, 10) (-10), Insert (0, 20) 10]

    -- it "CaseM2 empty" $ do
    --   --     A   B
    --   --     ├───┤
    --   --     ├───┤
    --   --     X   Y
    --   testInsertion [Insert (0, 10) 10, Insert (0, 10) 1]

    -- it "CaseM2 empty negating" $ do
    --   --     A   B
    --   --     ├───┤
    --   --     ├───┤
    --   --     X   Y
    --   testInsertion [Insert (0, 10) (-10), Insert (0, 10) 10]

    -- it "CaseM2 non-immediate" $ do
    --   --     A   B
    --   --     ├───┤
    --   --     ├───┤    ├───┤
    --   --     X   Y    Z   W
    --   testInsertion [Insert (0, 10) 10, Insert (20, 30) 2, Insert (0, 10) 1]

    -- it "CaseM2 immediate" $ do
    --   --     A   B
    --   --     ├───┤
    --   --     ├───┼───┤
    --   --     X   Y   W
    --   testInsertion [Insert (0, 10) 10, Insert (10, 20) 2, Insert (0, 10) 1]

    -- it "CaseM2 immediate negating" $ do
    --   --     A   B
    --   --     ├───┤
    --   --     ├───┼───┤
    --   --     X   Y   W
    --   testInsertion [Insert (0, 10) (-10), Insert (10, 20) 2, Insert (0, 10) 10]

    -- it "CaseM2 immediate merging" $ do
    --   --     A   B
    --   --     ├───┤
    --   --     ├───┼───┤
    --   --     X   Y   W
    --   testInsertion [Insert (0, 10) 10, Insert (10, 20) 20, Insert (0, 10) 10]

    -- it "CaseM3 empty" $ do
    --   --     A       B
    --   --     ├───────┤
    --   --     ├───┤
    --   --     X   Y
    --   testInsertion [Insert (0, 20) 10, Insert (0, 10) 1]

    -- it "CaseM3 empty negating" $ do
    --   --     A       B
    --   --     ├───────┤
    --   --     ├───┤
    --   --     X   Y
    --   testInsertion [Insert (0, 20) (-10), Insert (0, 10) 10]

    -- it "CaseM3 non-immediate 1" $ do
    --   --     A       B
    --   --     ├───────┤
    --   --     ├───┤       ├───┤
    --   --     X   Y       Z   W
    --   testInsertion [Insert (0, 20) 10, Insert (30, 40) 2, Insert (0, 10) 1]

    -- it "CaseM3 non-immediate 2" $ do
    --   --     A       B
    --   --     ├───────┤
    --   --     ├───┤   ├───┤
    --   --     X   Y   Z   W
    --   testInsertion [Insert (0, 20) 10, Insert (20, 30) 2, Insert (0, 10) 1]

    -- it "CaseM3 non-immediate 3" $ do
    --   --     A           B
    --   --     ├───────────┤
    --   --     ├───┤   ├───────┤
    --   --     X   Y   Z       W
    --   testInsertion [Insert (0, 30) 10, Insert (20, 40) 2, Insert (0, 10) 1]

    -- it "CaseM3 non-immediate 4" $ do
    --   --     A           B
    --   --     ├───────────┤
    --   --     ├───┤   ├───┤
    --   --     X   Y   Z   W
    --   testInsertion [Insert (0, 30) 10, Insert (20, 30) 2, Insert (0, 10) 1]

    -- it "CaseM3 non-immediate 5" $ do
    --   --     A               B
    --   --     ├───────────────┤
    --   --     ├───┤   ├───┤
    --   --     X   Y   Z   W
    --   testInsertion [Insert (0, 40) 10, Insert (20, 30) 2, Insert (0, 10) 1]

    -- it "CaseM3 immediate 1" $ do
    --   --     A       B
    --   --     ├───────┤
    --   --     ├───┼───────┤
    --   --     X   Y       W
    --   testInsertion [Insert (0, 20) 10, Insert (10, 30) 2, Insert (0, 10) 1]

    -- it "CaseM3 immediate 2" $ do
    --   --     A       B
    --   --     ├───────┤
    --   --     ├───┼───┤
    --   --     X   Y   W
    --   testInsertion [Insert (0, 20) 10, Insert (10, 20) 2, Insert (0, 10) 1]

    -- it "CaseM3 immediate 3" $ do
    --   --     A           B
    --   --     ├───────────┤
    --   --     ├───┼───┤
    --   --     X   Y   W
    --   testInsertion [Insert (0, 30) 10, Insert (10, 20) 2, Insert (0, 10) 1]

    -- it "CaseR5" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───────────┤
    --   --     X           Y
    --   testInsertion [Insert (10, 20) 10, Insert (0, 30) 1]

    -- it "CaseR5 negating" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───────────┤
    --   --     X           Y
    --   testInsertion [Insert (10, 20) (-10), Insert (0, 30) 10]

    -- it "CaseR4 empty" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───────┤
    --   --     X       Y
    --   testInsertion [Insert (10, 20) 10, Insert (0, 20) 1]

    -- it "CaseR4 empty negating" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───────┤
    --   --     X       Y
    --   testInsertion [Insert (10, 20) (-10), Insert (0, 20) 10]

    -- it "CaseR4 non-immediate" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───────┤   ├───┤
    --   --     X       Y   Z   W
    --   testInsertion [Insert (10, 20) 10, Insert (30, 40) 2, Insert (0, 20) 1]

    -- it "CaseR4 immediate" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───────┼───┤
    --   --     X       Y   W
    --   testInsertion [Insert (10, 20) 10, Insert (20, 30) 2, Insert (0, 20) 1]

    -- it "CaseR4 immediate merging" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───────┼───┤
    --   --     X       Y   W
    --   testInsertion [Insert (10, 20) 10, Insert (20, 30) 20, Insert (0, 20) 10]

    -- it "CaseR4 immediate negating" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───────┼───┤
    --   --     X       Y   W
    --   testInsertion [Insert (10, 20) (-10), Insert (20, 30) 20, Insert (0, 20) 10]

    -- it "CaseR3 empty" $ do
    --   --         A       B
    --   --         ├───────┤
    --   --     ├───────┤
    --   --     X       Y
    --   testInsertion [Insert (10, 30) 10, Insert (0, 20) 1]

    -- it "CaseR3 empty negating" $ do
    --   --         A       B
    --   --         ├───────┤
    --   --     ├───────┤
    --   --     X       Y
    --   testInsertion [Insert (10, 30) (-10), Insert (0, 20) 10]

    -- it "CaseR3 non-immediate 1" $ do
    --   --         A       B
    --   --         ├───────┤
    --   --     ├───────┤       ├───┤
    --   --     X       Y       Z   W
    --   testInsertion [Insert (10, 30) 10, Insert (40, 50) 2, Insert (0, 20) 1]

    -- it "CaseR3 non-immediate 2" $ do
    --   --         A       B
    --   --         ├───────┤
    --   --     ├───────┤   ├───┤
    --   --     X       Y   Z   W
    --   testInsertion [Insert (10, 30) 10, Insert (30, 40) 2, Insert (0, 20) 1]

    -- it "CaseR3 non-immediate 3" $ do
    --   --         A           B
    --   --         ├───────────┤
    --   --     ├───────┤   ├───────┤
    --   --     X       Y   Z       W
    --   testInsertion [Insert (10, 40) 10, Insert (30, 50) 2, Insert (0, 20) 1]

    -- it "CaseR3 non-immediate 4" $ do
    --   --         A           B
    --   --         ├───────────┤
    --   --     ├───────┤   ├───┤
    --   --     X       Y   Z   W
    --   testInsertion [Insert (10, 40) 10, Insert (30, 40) 2, Insert (0, 20) 1]

    -- it "CaseR3 non-immediate 5" $ do
    --   --         A               B
    --   --         ├───────────────┤
    --   --     ├───────┤   ├───┤
    --   --     X       Y   Z   W
    --   testInsertion [Insert (10, 50) 10, Insert (30, 40) 2, Insert (0, 20) 1]

    -- it "CaseR3 immediate 1" $ do
    --   --         A       B
    --   --         ├───────┤
    --   --     ├───────┼───────┤
    --   --     X       Y       W
    --   testInsertion [Insert (10, 30) 10, Insert (20, 40) 2, Insert (0, 20) 1]

    -- it "CaseR3 immediate 2" $ do
    --   --         A       B
    --   --         ├───────┤
    --   --     ├───────┼───┤
    --   --     X       Y   W
    --   testInsertion [Insert (10, 30) 10, Insert (20, 30) 2, Insert (0, 20) 1]

    -- it "CaseR3 immediate 3" $ do
    --   --         A           B
    --   --         ├───────────┤
    --   --     ├───────┼───┤
    --   --     X       Y   W
    --   testInsertion [Insert (10, 40) 10, Insert (20, 30) 2, Insert (0, 20) 1]

    -- it "CaseR2 empty" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───┤
    --   --     X   Y
    --   testInsertion [Insert (10, 20) 10, Insert (0, 10) 1]

    -- it "CaseR2 empty merging" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───┤
    --   --     X   Y
    --   testInsertion [Insert (10, 20) 10, Insert (0, 10) 10]

    -- it "CaseR2 non-immediate 1" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───┤       ├───┤
    --   --     X   Y       Z   W
    --   testInsertion [Insert (10, 20) 10, Insert (30, 40) 2, Insert (0, 10) 1]

    -- it "CaseR2 non-immediate 2" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───┤   ├───┤
    --   --     X   Y   Z   W
    --   testInsertion [Insert (10, 20) 10, Insert (20, 30) 2, Insert (0, 10) 1]

    -- it "CaseR2 non-immediate 3" $ do
    --   --         A       B
    --   --         ├───────┤
    --   --     ├───┤   ├───────┤
    --   --     X   Y   Z       W
    --   testInsertion [Insert (10, 30) 10, Insert (20, 40) 2, Insert (0, 10) 1]

    -- it "CaseR2 non-immediate 4" $ do
    --   --         A       B
    --   --         ├───────┤
    --   --     ├───┤   ├───┤
    --   --     X   Y   Z   W
    --   testInsertion [Insert (10, 30) 10, Insert (20, 30) 2, Insert (0, 10) 1]

    -- it "CaseR2 non-immediate 5" $ do
    --   --         A           B
    --   --         ├───────────┤
    --   --     ├───┤   ├───┤
    --   --     X   Y   Z   W
    --   testInsertion [Insert (10, 40) 10, Insert (20, 30) 2, Insert (0, 10) 1]

    -- it "CaseR2 immediate 1" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───┼───────┤
    --   --     X   Y       W
    --   testInsertion [Insert (10, 20) 10, Insert (10, 30) 2, Insert (0, 10) 1]

    -- it "CaseR2 immediate 1 merging 1" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───┼───────┤
    --   --     X   Y       W
    --   testInsertion [Insert (10, 20) 10, Insert (10, 30) 10, Insert (0, 10) 20]

    -- it "CaseR2 immediate 1 merging 2" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───┼───┤
    --   --     X   Y   W
    --   testInsertion [Insert (10, 20) 10, Insert (10, 20) 10, Insert (0, 10) 20]

    -- it "CaseR2 immediate 1 merging 3" $ do
    --   --         A       B
    --   --         ├───────┤
    --   --     ├───┼───┤
    --   --     X   Y   W
    --   testInsertion [Insert (10, 30) 10, Insert (10, 20) 10, Insert (0, 10) 20]

    -- it "CaseR2 immediate 2" $ do
    --   --         A   B
    --   --         ├───┤
    --   --     ├───┼───┤
    --   --     X   Y   W
    --   testInsertion [Insert (10, 20) 10, Insert (10, 20) 2, Insert (0, 10) 1]

    -- it "CaseR2 immediate 3" $ do
    --   --         A       B
    --   --         ├───────┤
    --   --     ├───┼───┤
    --   --     X   Y   W
    --   testInsertion [Insert (10, 30) 10, Insert (10, 20) 2, Insert (0, 10) 1]

    -- it "CaseR1 empty" $ do
    --   --             A   B
    --   --             ├───┤
    --   --     ├───┤
    --   --     X   Y
    --   testInsertion [Insert (20, 30) 10, Insert (0, 10) 1]

    -- it "CaseR1 non-immediate 1" $ do
    --   --             A   B
    --   --             ├───┤
    --   --     ├───┤           ├───┤
    --   --     X   Y           Z   W
    --   testInsertion [Insert (20, 30) 10, Insert (40, 50) 2, Insert (0, 10) 1]

    -- it "CaseR1 non-immediate 2" $ do
    --   --             A   B
    --   --             ├───┤
    --   --     ├───┤       ├───┤
    --   --     X   Y       Z   W
    --   testInsertion [Insert (20, 30) 10, Insert (30, 40) 2, Insert (0, 10) 1]

    -- it "CaseR1 non-immediate 3" $ do
    --   --             A       B
    --   --             ├───────┤
    --   --     ├───┤       ├───────┤
    --   --     X   Y       Z       W
    --   testInsertion [Insert (20, 40) 10, Insert (30, 50) 2, Insert (0, 10) 1]

    -- it "CaseR1 non-immediate 4" $ do
    --   --             A       B
    --   --             ├───────┤
    --   --     ├───┤       ├───┤
    --   --     X   Y       Z   W
    --   testInsertion [Insert (20, 40) 10, Insert (30, 40) 2, Insert (0, 10) 1]

    -- it "CaseR1 non-immediate 5" $ do
    --   --             A           B
    --   --             ├───────────┤
    --   --     ├───┤       ├───┤
    --   --     X   Y       Z   W
    --   testInsertion [Insert (20, 50) 10, Insert (30, 40) 2, Insert (0, 10) 1]

    it "should preserve invariants after applying randomized insertions" $ do
      property testInsertion

    it "should handle cases like these" $ do
      testInsertion [Insert (10, 20) (-10), Insert (10, 20) 10, Insert (0, 30) 20]
      testInsertion [Insert (24, 28) (-24), Insert (24, 29) 24, Insert (23, 27) (-65)]
      testInsertion [Insert (10, 40) 10, Insert (0, 30) 100, Insert (10, 20) (-10)]

  describe "singleton" $ do
    it "should result in a valid IntervalSet" $ do
      property $ \(start, end, count) -> do
        case IntervalSet.singleton (start, end) (count :: Prime 17) of
          Nothing -> return ()
          Just xs -> IntervalSet.validate xs `shouldBe` Nothing

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

-- ([-84$0, -48$1, -71$2, -82$3, -91$4, -34$5, -37$6, -9$7, 71$8, 47$9, 98$10, 38$11, 51($12 ~ $13), 32$14, 213$15, 181$16, 41($17 ~ $18), 9($19 ~ $20), -87$22, -120$23, -33$24, 36$25, 21$26, 100$27, 157$28, 205$29, 57$30, 115$31, 33($32 ~ $33), 58$34, -6$35, 7$36, 64$37, 21$38, 15$39, -92$40, -12$41, -53($42 ~ $43), -138($44 ~ $45), -75($46 ~ $47), 63($47 ~ $48), 115$49, 49($50 ~ $51), 79$52, 84$53, 167$54, 90$55, 146($56 ~ $57), 90$58, 74($61 ~ $63), 69($64 ~ $65), 12$67, -44($68 ~ $69), -98($70 ~ $71), 43($72 ~ $73), 83$74, 125$75, -53$76, 7$77, -175$78, 14($79 ~ $80), -104$81, -209$82, -124$83, -61$84, 77$85, 143($86 ~ $87), 41$88, -33$89, 3($90 ~ $91), 83($92 ~ $93), 80$94, 80$97, -91$99, -80($100 ~ $101), -42$102, 49$103],0)

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