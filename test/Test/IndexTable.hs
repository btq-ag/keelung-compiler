{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.IndexTable (tests, run) where

import Control.Monad (forM_)
import Data.IntMap.Strict qualified as IntMap
import Keelung
import Keelung.Compiler.Compile.IndexTable qualified as IndexTable
import Keelung.Data.Constraint
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.Linker (constructOccurrences, reindexRef)
import Test.Hspec
import Test.Optimization.Util (executeGF181)
import qualified Data.Sequence as Seq

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
      let occurrences = IntMap.fromList [(0, 1), (2, 0), (3, 2), (4, 1), (5, 3)]
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

  describe "fromOccurrences" $ do
    it "add + assertion" $ do
      (_cm, cm) <- executeGF181 $ do
        x <- inputUInt @4 Public
        assert $ 2 `eq` (x + 1)
      let occurrences = constructOccurrences (cmCounters cm) (cmOccurrenceF cm) (cmOccurrenceB cm) (cmOccurrenceU cm)
      let inputVar = RefUI 4 0
      reindexRef occurrences (B (RefUBit 4 inputVar 0)) (1 :: GF181) `shouldBe` Seq.singleton (0, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar 1)) (1 :: GF181) `shouldBe` Seq.singleton (1, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar 2)) (1 :: GF181) `shouldBe` Seq.singleton (2, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar 3)) (1 :: GF181) `shouldBe` Seq.singleton (3, 1)
      let intermediateB = RefBX 0
      reindexRef occurrences (B intermediateB) (1 :: GF181) `shouldBe` Seq.singleton (4, 1)
      let intermediate4 = RefUX 4 0
      reindexRef occurrences (B (RefUBit 4 intermediate4 0)) (1 :: GF181) `shouldBe` Seq.singleton (5, 1)
      reindexRef occurrences (B (RefUBit 4 intermediate4 1)) (1 :: GF181) `shouldBe` Seq.singleton (6, 1)
      reindexRef occurrences (B (RefUBit 4 intermediate4 2)) (1 :: GF181) `shouldBe` Seq.singleton (7, 1)
      reindexRef occurrences (B (RefUBit 4 intermediate4 3)) (1 :: GF181) `shouldBe` Seq.singleton (8, 1)

    it "Bit test / and 1" $ do
      (_, cm) <- executeGF181 $ do
        x <- inputUInt @4 Public
        y <- inputUInt @4 Private
        return $ (x .&. y) !!! 0
      let occurrences = constructOccurrences (cmCounters cm) (cmOccurrenceF cm) (cmOccurrenceB cm) (cmOccurrenceU cm)

      reindexRef occurrences (B (RefBO 0)) (1 :: GF181) `shouldBe` Seq.singleton (0, 1)
      let inputVar0 = RefUI 4 0
      reindexRef occurrences (B (RefUBit 4 inputVar0 0)) (1 :: GF181) `shouldBe` Seq.singleton (1, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar0 1)) (1 :: GF181) `shouldBe` Seq.singleton (2, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar0 2)) (1 :: GF181) `shouldBe` Seq.singleton (3, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar0 3)) (1 :: GF181) `shouldBe` Seq.singleton (4, 1)
      let inputVar1 = RefUP 4 0
      reindexRef occurrences (B (RefUBit 4 inputVar1 0)) (1 :: GF181) `shouldBe` Seq.singleton (5, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar1 1)) (1 :: GF181) `shouldBe` Seq.singleton (6, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar1 2)) (1 :: GF181) `shouldBe` Seq.singleton (7, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar1 3)) (1 :: GF181) `shouldBe` Seq.singleton (8, 1)
      let intermediateVar0 = RefUX 4 0
      reindexRef occurrences (B (RefUBit 4 intermediateVar0 0)) (1 :: GF181) `shouldBe` Seq.singleton (9, 1)
      reindexRef occurrences (B (RefUBit 4 intermediateVar0 1)) (1 :: GF181) `shouldBe` Seq.singleton (10, 1)
      reindexRef occurrences (B (RefUBit 4 intermediateVar0 2)) (1 :: GF181) `shouldBe` Seq.singleton (11, 1)
      reindexRef occurrences (B (RefUBit 4 intermediateVar0 3)) (1 :: GF181) `shouldBe` Seq.singleton (12, 1)

    it "Bit test / and 2" $ do
      (_, cm) <- executeGF181 $ do
        x <- inputUInt @4 Public
        y <- inputUInt @4 Private
        z <- inputUInt @4 Public
        return $ (x .&. y .&. z) !!! 0
      let occurrences = constructOccurrences (cmCounters cm) (cmOccurrenceF cm) (cmOccurrenceB cm) (cmOccurrenceU cm)

      reindexRef occurrences (B (RefBO 0)) (1 :: GF181) `shouldBe` Seq.singleton (0, 1)
      let inputVar0 = RefUI 4 0
      reindexRef occurrences (B (RefUBit 4 inputVar0 0)) (1 :: GF181) `shouldBe` Seq.singleton (1, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar0 1)) (1 :: GF181) `shouldBe` Seq.singleton (2, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar0 2)) (1 :: GF181) `shouldBe` Seq.singleton (3, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar0 3)) (1 :: GF181) `shouldBe` Seq.singleton (4, 1)
      let inputVar2 = RefUI 4 1
      reindexRef occurrences (B (RefUBit 4 inputVar2 0)) (1 :: GF181) `shouldBe` Seq.singleton (5, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar2 1)) (1 :: GF181) `shouldBe` Seq.singleton (6, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar2 2)) (1 :: GF181) `shouldBe` Seq.singleton (7, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar2 3)) (1 :: GF181) `shouldBe` Seq.singleton (8, 1)
      let inputVar1 = RefUP 4 0
      reindexRef occurrences (B (RefUBit 4 inputVar1 0)) (1 :: GF181) `shouldBe` Seq.singleton (9, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar1 1)) (1 :: GF181) `shouldBe` Seq.singleton (10, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar1 2)) (1 :: GF181) `shouldBe` Seq.singleton (11, 1)
      reindexRef occurrences (B (RefUBit 4 inputVar1 3)) (1 :: GF181) `shouldBe` Seq.singleton (12, 1)
      reindexRef occurrences (F (RefFX 0)) (1 :: GF181) `shouldBe` Seq.singleton (13, 1)
      reindexRef occurrences (F (RefFX 1)) (1 :: GF181) `shouldBe` Seq.singleton (14, 1)
      reindexRef occurrences (F (RefFX 2)) (1 :: GF181) `shouldBe` Seq.singleton (15, 1)
      reindexRef occurrences (F (RefFX 3)) (1 :: GF181) `shouldBe` Seq.singleton (16, 1)
      reindexRef occurrences (B (RefUBit 4 (RefUX 4 0) 0)) (1 :: GF181) `shouldBe` Seq.singleton (17, 1)
      reindexRef occurrences (B (RefUBit 4 (RefUX 4 0) 1)) (1 :: GF181) `shouldBe` Seq.singleton (18, 1)
      reindexRef occurrences (B (RefUBit 4 (RefUX 4 0) 2)) (1 :: GF181) `shouldBe` Seq.singleton (19, 1)
      reindexRef occurrences (B (RefUBit 4 (RefUX 4 0) 3)) (1 :: GF181) `shouldBe` Seq.singleton (20, 1)