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
          table = IndexTable.fromOccurrenceMap occurrences
      forM_ [0 .. 5] $ \i -> do
        IndexTable.reindex table i `shouldBe` i

    it "with 1 hole in the back" $ do
      let occurrences = IntMap.fromList $ zip [0 ..] [1, 2, 1, 3, 0, 0]
          table = IndexTable.fromOccurrenceMap occurrences
      forM_ [0 .. 3] $ \i -> do
        IndexTable.reindex table i `shouldBe` i

    it "with 1 hole in the middle" $ do
      let occurrences = IntMap.fromList $ zip [0 ..] [1, 0, 0, 2, 1, 3]
          table = IndexTable.fromOccurrenceMap occurrences

      forM_ [0] $ \i -> do
        IndexTable.reindex table i `shouldBe` i
      forM_ [3 .. 5] $ \i -> do
        IndexTable.reindex table i `shouldBe` i - 2

    it "with 1 hole in the front" $ do
      let occurrences = IntMap.fromList $ zip [0 ..] [0, 0, 0, 1, 2, 1, 3]
          table = IndexTable.fromOccurrenceMap occurrences

      forM_ [3 .. 6] $ \i -> do
        IndexTable.reindex table i `shouldBe` i - 3

    it "other cases" $ do
      let occurrences = IntMap.fromList $ zip [0 ..] [0, 1, 0, 1, 2, 0, 3]
          table = IndexTable.fromOccurrenceMap occurrences

      IndexTable.reindex table 1 `shouldBe` 0
      IndexTable.reindex table 3 `shouldBe` 1
      IndexTable.reindex table 4 `shouldBe` 2
      IndexTable.reindex table 6 `shouldBe` 3

  describe "merge" $ do
    it "1" $ do
      let occurrences = IntMap.fromList $ zip [0 ..] [0, 1, 0, 1, 2, 0, 3]
          table1 = IndexTable.fromOccurrenceMap occurrences
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
      let table1 = IndexTable.fromOccurrenceMap (IntMap.fromList (zip [0 ..] [0, 0, 0]))
          table2 = IndexTable.fromOccurrenceMap (IntMap.fromList (zip [0 ..] [2, 3, 0]))
          table3 = IndexTable.fromOccurrenceMap (IntMap.fromList (zip [0 ..] [2, 3, 0]))
          table = table1 <> table2 <> table3

      IndexTable.reindex table 3 `shouldBe` 0
      IndexTable.reindex table 4 `shouldBe` 1
      IndexTable.reindex table 6 `shouldBe` 2
      IndexTable.reindex table 7 `shouldBe` 3
