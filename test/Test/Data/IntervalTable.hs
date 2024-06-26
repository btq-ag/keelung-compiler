{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Data.IntervalTable (tests, run) where

import Control.Monad (forM_)
import Data.IntMap (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Keelung
import Keelung.Compiler.ConstraintModule (ConstraintModule)
import Keelung.Compiler.Linker (constructEnv, reindexRef, reindexSlice)
import Keelung.Compiler.Optimize.OccurU qualified as OccurU
import Keelung.Data.IntervalTable (IntervalTable (..))
import Keelung.Data.IntervalTable qualified as IntervalTable
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice (Slice))
import Test.Hspec
import Test.Util
import Keelung.Compiler.Util (powerOf2)

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests =
  describe "IntervalTable" $ do
    describe "reindex" $ do
      it "with no holes" $ do
        let env = IntMap.fromList $ zip [0 ..] [1, 2, 1, 3, 4, 1]
            table = IntervalTable.fromOccurrenceMap 1 (6, env)
        forM_ [0 .. 5] $ \i -> do
          IntervalTable.reindex table i `shouldBe` i

      it "with 1 hole in the back" $ do
        let env = IntMap.fromList $ zip [0 ..] [1, 2, 1, 3, 0, 0]
            table = IntervalTable.fromOccurrenceMap 1 (6, env)
        forM_ [0 .. 3] $ \i -> do
          IntervalTable.reindex table i `shouldBe` i

      it "with 1 hole in the middle" $ do
        let env = IntMap.fromList [(0, 1), (2, 0), (3, 2), (4, 1), (5, 3)]
            table = IntervalTable.fromOccurrenceMap 1 (6, env)

        forM_ [0] $ \i -> do
          IntervalTable.reindex table i `shouldBe` i
        forM_ [3 .. 5] $ \i -> do
          IntervalTable.reindex table i `shouldBe` i - 2

      it "with 1 hole in the front" $ do
        let env = IntMap.fromList $ zip [0 ..] [0, 0, 0, 1, 2, 1, 3]
            table = IntervalTable.fromOccurrenceMap 1 (7, env)

        forM_ [3 .. 6] $ \i -> do
          IntervalTable.reindex table i `shouldBe` i - 3

      it "other cases" $ do
        let env = IntMap.fromList $ zip [0 ..] [0, 1, 0, 1, 2, 0, 3]
            table = IntervalTable.fromOccurrenceMap 1 (7, env)

        IntervalTable.reindex table 1 `shouldBe` 0
        IntervalTable.reindex table 3 `shouldBe` 1
        IntervalTable.reindex table 4 `shouldBe` 2
        IntervalTable.reindex table 6 `shouldBe` 3

      it "with different bit widths 1" $ do
        let env = IntMap.fromList $ zip [0 ..] [0, 1, 2, 1, 2, 0, 3]
            table = IntervalTable.fromOccurrenceMap 2 (7, env)

        -- 01234567890123
        -- __xxxxxxxx__xx
        -- [(2, 2), (12, 4)]
        -- xxxxxxxxxx

        IntervalTable.reindex table 2 `shouldBe` 0
        IntervalTable.reindex table 4 `shouldBe` 2
        IntervalTable.reindex table 6 `shouldBe` 4
        IntervalTable.reindex table 8 `shouldBe` 6
        IntervalTable.reindex table 12 `shouldBe` 8

      it "with different bit widths 2" $ do
        let env = IntMap.fromList $ zip [0 ..] [0, 1, 2, 1, 2, 0, 3]
            table = IntervalTable.fromOccurrenceMap 2 (7, env) <> IntervalTable.fromOccurrenceMap 3 (7, env)

        -- 01234567890123456789012345678901234
        -- __xxxxxxxx__xx___xxxxxxxxxxxx___xxx
        -- [(2, 2), (12, 4), (17, 7), (32, 10)]
        -- xxxxxxxxxxxxxxxxxxxxxxxxx

        IntervalTable.reindex table 2 `shouldBe` 0
        IntervalTable.reindex table 4 `shouldBe` 2
        IntervalTable.reindex table 6 `shouldBe` 4
        IntervalTable.reindex table 8 `shouldBe` 6
        IntervalTable.reindex table 12 `shouldBe` 8
        IntervalTable.reindex table 17 `shouldBe` 10
        IntervalTable.reindex table 20 `shouldBe` 13
        IntervalTable.reindex table 23 `shouldBe` 16
        IntervalTable.reindex table 26 `shouldBe` 19
        IntervalTable.reindex table 32 `shouldBe` 22

    describe "merge" $ do
      it "Field or Boolean: 1" $ do
        let table1 = IntervalTable.fromOccurrenceMap 1 (7, IntMap.fromList $ zip [0 ..] [0, 1, 0, 1, 2, 0, 3])
            table = table1 <> table1

        map (IntervalTable.reindex table) [1, 3, 4, 6, 8, 10, 11, 13] `shouldBe` [0 .. 7]

      it "Field or Boolean: 2" $ do
        let table1 = IntervalTable.fromOccurrenceMap 1 (3, IntMap.fromList (zip [0 ..] [0, 0, 0]))
            table2 = IntervalTable.fromOccurrenceMap 1 (3, IntMap.fromList (zip [0 ..] [2, 3, 0]))
            table3 = IntervalTable.fromOccurrenceMap 1 (3, IntMap.fromList (zip [0 ..] [2, 3, 0]))
            table = table1 <> table2 <> table3

        map (IntervalTable.reindex table) [3, 4, 6, 7] `shouldBe` [0 .. 3]

      it "UInt 4" $ do
        let table1 = IntervalTable 4 2 (IntMap.fromList [(0, (2, 0))])
            table2 = IntervalTable 4 2 (IntMap.fromList [(2, (2, 2))])
            table = table1 <> table2

        map (IntervalTable.reindex table) [0, 1, 6, 7] `shouldBe` [0 .. 3]

    describe "from OccurU" $ do
      it "1" $ do
        let occurU = OccurU.increase 4 1 (2, 4) $ OccurU.increase 4 0 (0, 2) OccurU.new
        let tables = OccurU.toIntervalTables occurU
        case IntMap.lookup 4 tables of
          Nothing -> error "should not happen"
          Just table -> do
            map (IntervalTable.reindex table) [0, 1, 6, 7] `shouldBe` [0 .. 3]

      it "2" $ do
        let occurU = OccurU.increase 4 1 (1, 3) $ OccurU.increase 4 1 (2, 4) $ OccurU.increase 4 0 (0, 2) OccurU.new
        let tables = OccurU.toIntervalTables occurU
        case IntMap.lookup 4 tables of
          Nothing -> error "should not happen"
          Just table -> do
            map (IntervalTable.reindex table) [0, 1, 5, 6, 7] `shouldBe` [0 .. 4]

    describe "fromEnv" $ do
      it "add + assertion" $ do
        let program = do
              x <- inputUInt @4 Public
              assert $ 2 `eq` (x + 1)
        cm <- compileAsConstraintModule gf181 program :: IO (ConstraintModule GF181)
        let env = constructEnv cm
        let inputVar = RefUI 4 0
        reindexSlice env (Slice inputVar 0 4) (1 :: GF181) `shouldBe` buildIntMap 4 0
        let intermediateB = RefBX 0
        reindexRef env (B intermediateB) `shouldBe` 4
        let intermediate4 = RefUX 4 0
        reindexSlice env (Slice intermediate4 0 4) (1 :: GF181) `shouldBe` buildIntMap 4 5

      it "Bit test / and 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              return $ (x .&. y) !!! 0
        cm <- compileAsConstraintModule gf181 program :: IO (ConstraintModule GF181)
        let env = constructEnv cm
        reindexRef env (B (RefBO 0)) `shouldBe` 0
        let inputVar0 = RefUI 4 0
        reindexSlice env (Slice inputVar0 0 4) (1 :: GF181) `shouldBe` buildIntMap 4 1
        let inputVar1 = RefUP 4 0
        reindexSlice env (Slice inputVar1 0 4) (1 :: GF181) `shouldBe` buildIntMap 4 5
        let intermediateVar0 = RefUX 4 0
        reindexSlice env (Slice intermediateVar0 0 4) (1 :: GF181) `shouldBe` buildIntMap 4 12

      it "Bit test / and 2" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              z <- inputUInt @4 Public
              return $ (x .&. y .&. z) !!! 0
        cm <- compileAsConstraintModule gf181 program :: IO (ConstraintModule GF181)
        let env = constructEnv cm

        reindexRef env (B (RefBO 0)) `shouldBe` 0
        let inputVar0 = RefUI 4 0
        reindexSlice env (Slice inputVar0 0 4) (1 :: GF181) `shouldBe` buildIntMap 4 1
        let inputVar2 = RefUI 4 1
        reindexSlice env (Slice inputVar2 0 4) (1 :: GF181) `shouldBe` buildIntMap 4 5
        let inputVar1 = RefUP 4 0
        reindexSlice env (Slice inputVar1 0 4) (1 :: GF181) `shouldBe` buildIntMap 4 9
        reindexRef env (F (RefFX 0)) `shouldBe` 13

buildIntMap :: (Integral n, GaloisField n) => Width -> Int -> IntMap n
buildIntMap w i = IntMap.fromList [(j, powerOf2 (j - i)) | j <- [i .. i + w - 1]]