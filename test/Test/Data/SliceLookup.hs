{-# LANGUAGE FlexibleInstances #-}

module Test.Data.SliceLookup
  ( tests,
    run,
  )
where

import Data.IntMap qualified as IntMap
import Keelung (widthOf)
import Keelung.Data.SliceLookup (SliceLookup (..))
import Keelung.Data.SliceLookup qualified as SliceLookup
import Test.Arbitrary
import Test.Hspec
import Test.QuickCheck

--------------------------------------------------------------------------------

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "SliceLookup" $ do
  it "should be valid" $ do
    property $ \sliceLookup -> do
      SliceLookup.isValid sliceLookup `shouldBe` True

  describe "widthOf SliceLookup" $ do
    it "should be the sum of all lengths of its segments" $ do
      property $ \sliceLookup -> do
        widthOf sliceLookup `shouldBe` sum (widthOf <$> IntMap.elems (lookupSegments sliceLookup))

  describe "split & merge" $ do
    it "should result in valid SliceLookups after normalization" $ do
      let genParam = do
            sliceLookup <- arbitrary
            index <- chooseInt (0, widthOf sliceLookup - 1)
            pure (sliceLookup, index)
      forAll genParam $ \(sliceLookup, index) -> do
        let (ref, sliceLookup1, sliceLookup2) = SliceLookup.split index sliceLookup
        SliceLookup.isValid (SliceLookup ref sliceLookup1) `shouldBe` True
        SliceLookup.isValid (SliceLookup ref sliceLookup2) `shouldBe` True
        SliceLookup.isValid (SliceLookup.normalize (SliceLookup ref (sliceLookup1 <> sliceLookup2))) `shouldBe` True

    it "should preserve lengths of segments (`(+) . widthOf . split = widthOf`)" $ do
      let genParam = do
            sliceLookup <- arbitrary
            index <- chooseInt (0, widthOf sliceLookup - 1)
            pure (sliceLookup, index)
      forAll genParam $ \(sliceLookup, index) -> do
        let (ref, sliceLookup1, sliceLookup2) = SliceLookup.split index sliceLookup
        widthOf (SliceLookup ref sliceLookup1) + widthOf (SliceLookup ref sliceLookup2) `shouldBe` widthOf sliceLookup

  describe "splice" $ do
    it "should result in a SliceLookup of the same width as of the interval" $ do
      let genParam = do
            sliceLookup <- arbitrary
            let ref = lookupRefU sliceLookup
            start <- chooseInt (0, widthOf ref)
            end <- chooseInt (start, widthOf ref)
            pure (sliceLookup, (start, end))
      forAll genParam $ \(sliceLookup, (start, end)) -> do
        let result = SliceLookup.splice (start, end) sliceLookup
        widthOf result `shouldBe` end - start

  describe "normalize" $ do
    it "should be the coequalizer of `merge . split` and `id`" $ do
      let genParam = do
            sliceLookup <- arbitrary
            index <- chooseInt (0, (widthOf sliceLookup - 1) `max` 0)
            pure (sliceLookup, index)
      forAll genParam $ \(sliceLookup, index) -> do
        let (ref, sliceLookup1, sliceLookup2) = SliceLookup.split index sliceLookup
        SliceLookup.normalize (SliceLookup ref (sliceLookup1 <> sliceLookup2)) `shouldBe` SliceLookup.normalize sliceLookup

    it "should result in valid SliceLookups" $ do
      property $ \sliceLookup -> do
        SliceLookup.isValid (SliceLookup.normalize sliceLookup) `shouldBe` True

  describe "fromSegment" $ do
    it "should result in valid SliceLookups" $ do
      let genParam = do
            slice <- arbitrary
            segment <- arbitrarySegmentOfSlice slice
            pure (slice, segment)
      forAll genParam $ \(slice, segment) -> do
        let sliceLookup = SliceLookup.fromSegment slice segment
        SliceLookup.isValid sliceLookup `shouldBe` True
