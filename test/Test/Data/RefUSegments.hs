{-# LANGUAGE FlexibleInstances #-}

module Test.Data.RefUSegments
  ( tests,
    run,
  )
where

import Keelung (widthOf)
import Keelung.Data.RefUSegments (RefUSegments (..))
import Keelung.Data.RefUSegments qualified as RefUSegments
import Test.Arbitrary
import Test.Hspec
import Test.QuickCheck

--------------------------------------------------------------------------------

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "RefUSegments" $ do
  it "should be valid" $ do
    property $ \sliceLookup -> do
      RefUSegments.isValid sliceLookup `shouldBe` True

  describe "widthOf RefUSegments" $ do
    it "should be the sum of all lengths of its segments" $ do
      property $ \sliceLookup -> do
        widthOf sliceLookup `shouldBe` sum (widthOf <$> RefUSegments.toList sliceLookup)

  describe "split & merge" $ do
    it "should result in valid RefUSegmentss after normalization" $ do
      let genParam = do
            sliceLookup <- arbitrary
            index <- chooseInt (0, widthOf sliceLookup - 1)
            pure (sliceLookup, index)
      forAll genParam $ \(sliceLookup, index) -> do
        let (ref, sliceLookup1, sliceLookup2) = RefUSegments.split index sliceLookup
        RefUSegments.isValid (RefUSegments ref sliceLookup1) `shouldBe` True
        RefUSegments.isValid (RefUSegments ref sliceLookup2) `shouldBe` True
        RefUSegments.isValid (RefUSegments.normalize (RefUSegments ref (sliceLookup1 <> sliceLookup2))) `shouldBe` True

    it "should preserve lengths of segments (`(+) . widthOf . split = widthOf`)" $ do
      let genParam = do
            sliceLookup <- arbitrary
            index <- chooseInt (0, widthOf sliceLookup - 1)
            pure (sliceLookup, index)
      forAll genParam $ \(sliceLookup, index) -> do
        let (ref, sliceLookup1, sliceLookup2) = RefUSegments.split index sliceLookup
        widthOf (RefUSegments ref sliceLookup1) + widthOf (RefUSegments ref sliceLookup2) `shouldBe` widthOf sliceLookup

  describe "splice" $ do
    it "should result in a RefUSegments of the same width as of the interval" $ do
      let genParam = do
            sliceLookup <- arbitrary
            start <- chooseInt (0, widthOf sliceLookup)
            end <- chooseInt (start, widthOf sliceLookup)
            pure (sliceLookup, (start, end))
      forAll genParam $ \(sliceLookup, (start, end)) -> do
        let result = RefUSegments.splice (start, end) sliceLookup
        widthOf result `shouldBe` end - start

  describe "normalize" $ do
    it "should be the coequalizer of `merge . split` and `id`" $ do
      let genParam = do
            sliceLookup <- arbitrary
            index <- chooseInt (0, (widthOf sliceLookup - 1) `max` 0)
            pure (sliceLookup, index)
      forAll genParam $ \(sliceLookup, index) -> do
        let (ref, sliceLookup1, sliceLookup2) = RefUSegments.split index sliceLookup
        RefUSegments.normalize (RefUSegments ref (sliceLookup1 <> sliceLookup2)) `shouldBe` RefUSegments.normalize sliceLookup

    it "should result in valid RefUSegmentss" $ do
      property $ \sliceLookup -> do
        RefUSegments.isValid (RefUSegments.normalize sliceLookup) `shouldBe` True

  describe "fromSegment" $ do
    it "should result in valid RefUSegmentss" $ do
      let genParam = do
            slice <- arbitrary
            segment <- arbitrarySegmentOfSlice slice
            pure (slice, segment)
      forAll genParam $ \(slice, segment) -> do
        let sliceLookup = RefUSegments.fromSegment slice segment
        RefUSegments.isValid sliceLookup `shouldBe` True
