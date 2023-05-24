module Test.IndexTable (tests, run) where

import Control.Monad (forM_)
import Data.IntMap.Strict qualified as IntMap
import Keelung.Compiler.Compile.IndexTable qualified as IndexTable
import Test.Hspec

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "reindex" $ do
    it "with no holes" $ do
      let occurrences = IntMap.fromList $ zip [0 ..] [1, 2, 1, 3, 4, 1]
          table = IndexTable.fromOccurrenceMap 1 (6, occurrences)
      forM_ [0 .. 5] $ \i -> do
        IndexTable.reindex table i `shouldBe` i

    it "with 1 hole in the back" $ do
      let occurrences = IntMap.fromList $ zip [0 ..] [1, 2, 1, 3, 0, 0]
          table = IndexTable.fromOccurrenceMap 1 (6, occurrences)
      forM_ [0 .. 3] $ \i -> do
        IndexTable.reindex table i `shouldBe` i

    it "with 1 hole in the middle" $ do
      let occurrences = IntMap.fromList [(0,1),(2,0),(3,2),(4,1),(5,3)]
          table = IndexTable.fromOccurrenceMap 1 (6, occurrences)

      forM_ [0] $ \i -> do
        IndexTable.reindex table i `shouldBe` i
      forM_ [3 .. 5] $ \i -> do
        IndexTable.reindex table i `shouldBe` i - 2

    it "with 1 hole in the front" $ do
      let occurrences = IntMap.fromList $ zip [0 ..] [0, 0, 0, 1, 2, 1, 3]
          table = IndexTable.fromOccurrenceMap 1 (7, occurrences)

      forM_ [3 .. 6] $ \i -> do
        IndexTable.reindex table i `shouldBe` i - 3

    it "other cases" $ do
      let occurrences = IntMap.fromList $ zip [0 ..] [0, 1, 0, 1, 2, 0, 3]
          table = IndexTable.fromOccurrenceMap 1 (7, occurrences)


      IndexTable.reindex table 1 `shouldBe` 0
      IndexTable.reindex table 3 `shouldBe` 1
      IndexTable.reindex table 4 `shouldBe` 2
      IndexTable.reindex table 6 `shouldBe` 3

    it "with different bit widths 1" $ do
      let occurrences = IntMap.fromList $ zip [0 ..] [0, 1, 2, 1, 2, 0, 3]
          table = IndexTable.fromOccurrenceMap 2 (7, occurrences)

      -- 01234567890123
      -- __xxxxxxxx__xx
      -- [(2, 2), (12, 4)]
      -- xxxxxxxxxx

      IndexTable.reindex table 2 `shouldBe` 0
      IndexTable.reindex table 4 `shouldBe` 2
      IndexTable.reindex table 6 `shouldBe` 4
      IndexTable.reindex table 8 `shouldBe` 6
      IndexTable.reindex table 12 `shouldBe` 8

    it "with different bit widths 2" $ do
      let occurrences = IntMap.fromList $ zip [0 ..] [0, 1, 2, 1, 2, 0, 3]
          table = IndexTable.fromOccurrenceMap 2 (7, occurrences) <> IndexTable.fromOccurrenceMap 3 (7, occurrences)

      -- 01234567890123456789012345678901234
      -- __xxxxxxxx__xx___xxxxxxxxxxxx___xxx
      -- [(2, 2), (12, 4), (17, 7), (32, 10)]
      -- xxxxxxxxxxxxxxxxxxxxxxxxx

      IndexTable.reindex table 2 `shouldBe` 0
      IndexTable.reindex table 4 `shouldBe` 2
      IndexTable.reindex table 6 `shouldBe` 4
      IndexTable.reindex table 8 `shouldBe` 6
      IndexTable.reindex table 12 `shouldBe` 8
      IndexTable.reindex table 17 `shouldBe` 10
      IndexTable.reindex table 20 `shouldBe` 13
      IndexTable.reindex table 23 `shouldBe` 16
      IndexTable.reindex table 26 `shouldBe` 19
      IndexTable.reindex table 32 `shouldBe` 22

  describe "merge" $ do
    it "1" $ do
      let occurrences = IntMap.fromList $ zip [0 ..] [0, 1, 0, 1, 2, 0, 3]
          table1 = IndexTable.fromOccurrenceMap 1 (7, occurrences)
          table = table1 <> table1

      IndexTable.reindex table 1 `shouldBe` 0
      IndexTable.reindex table 3 `shouldBe` 1
      IndexTable.reindex table 4 `shouldBe` 2
      IndexTable.reindex table 6 `shouldBe` 3
      IndexTable.reindex table 8 `shouldBe` 4
      IndexTable.reindex table 10 `shouldBe` 5
      IndexTable.reindex table 11 `shouldBe` 6
      IndexTable.reindex table 13 `shouldBe` 7

    it "2" $ do
      let table1 = IndexTable.fromOccurrenceMap 1 (3, IntMap.fromList (zip [0 ..] [0, 0, 0]))
          table2 = IndexTable.fromOccurrenceMap 1 (3, IntMap.fromList (zip [0 ..] [2, 3, 0]))
          table3 = IndexTable.fromOccurrenceMap 1 (3, IntMap.fromList (zip [0 ..] [2, 3, 0]))
          table = table1 <> table2 <> table3

      IndexTable.reindex table 3 `shouldBe` 0
      IndexTable.reindex table 4 `shouldBe` 1
      IndexTable.reindex table 6 `shouldBe` 2
      IndexTable.reindex table 7 `shouldBe` 3
