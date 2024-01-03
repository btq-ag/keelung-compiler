module Test.Relations.Slice where

import Keelung (widthOf)
import Keelung.Compiler.Relations.Slice qualified as SliceRelations
import Keelung.Data.Reference (RefU (..))
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U
import Keelung.Data.U qualified as U
import Test.Hspec
import Test.QuickCheck
import qualified Data.IntMap.Strict as IntMap

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "SliceRelations" $ do
  describe "SliceRelations.assign" $ do
    it "should return the assigned value on lookup" $ do
      let relations = SliceRelations.new
      let genParam = do
            ref <- arbitrary
            let width = widthOf ref
            start <- chooseInt (0, width - 1)
            end <- chooseInt (start, width)
            val <- U.new (end - start) <$> chooseInteger (0, 2 ^ (end - start) - 1)
            pure (ref, (start, end), val)
      forAll genParam $ \(ref, interval, val) -> do
        print (ref, interval, val)
        let expectedSlice =  Slice.Slice ref (fst interval) (IntMap.singleton (fst interval) (Slice.Constant val)) -- Slice.mapInterval (const (Slice.Constant val)) interval (Slice.fromRefU ref)
        print ("expected", expectedSlice)

        let relations' = SliceRelations.assign ref interval val relations
        -- Slice.Slice ref (fst interval) (IntMap.singleton (fst interval) (Slice.Constant val))
        SliceRelations.lookup ref interval relations' `shouldBe` expectedSlice

-- widthOf slice `shouldBe` sum (widthOf <$> IntMap.elems (sliceSegments slice))

--   describe "split" $ do
--     it "should preserve lengths of segments (`(+) . widthOf . split = widthOf`)" $ do
--       let genParam = do
--             slice <- arbitrary
--             index <- chooseInt (0, widthOf slice - 1)
--             pure (slice, index)
--       forAll genParam $ \(slice, index) -> do
--         let (slice1, slice2) = Slice.split index slice
--         widthOf slice1 + widthOf slice2 `shouldBe` widthOf slice

--     it "should be the right inverse of `merge` (`merge . split = id`)" $ do
--       let genParam = do
--             slice <- arbitrary
--             index <- chooseInt (0, (widthOf slice - 1) `max` 0)
--             pure (slice, index)
--       forAll genParam $ \(slice, index) -> do
--         let (slice1, slice2) = Slice.split index slice
--         slice1 <> slice2 `shouldBe` slice

--   describe "normalize" $ do
--     it "should be the coequalizer of `merge . split` and `id`" $ do
--       let genParam = do
--             slice <- arbitrary
--             index <- chooseInt (0, (widthOf slice - 1) `max` 0)
--             pure (slice, index)
--       forAll genParam $ \(slice, index) -> do
--         let (slice1, slice2) = Slice.split index slice
--         Slice.normalize (slice1 <> slice2) `shouldBe` Slice.normalize slice

--   return ()

--------------------------------------------------------------------------------

instance Arbitrary RefU where
  arbitrary = do
    var <- chooseInt (0, 99)
    constructor <- elements [RefUO, RefUI, RefUP, RefUX]
    width <- chooseInt (1, 16)
    pure $ constructor width var

instance Arbitrary U where
  arbitrary = do
    width <- chooseInt (1, 16)
    value <- chooseInteger (0, 2 ^ width - 1)
    pure $ U.new width value