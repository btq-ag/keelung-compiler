{-# LANGUAGE FlexibleInstances #-}

module Test.Data.RefUSegments
  ( tests,
    run,
  )
where

import Keelung (widthOf)
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
    property $ \segments -> do
      RefUSegments.validate segments `shouldBe` []

  describe "widthOf RefUSegments" $ do
    it "should be the sum of all lengths of its segments" $ do
      property $ \segments -> do
        widthOf segments `shouldBe` sum (widthOf <$> RefUSegments.toIntMap segments)

  describe "splice" $ do
    it "should result in a RefUSegments of the same width as of the interval" $ do
      let genParam = do
            segments <- arbitrary
            start <- chooseInt (0, widthOf segments)
            end <- chooseInt (start, widthOf segments)
            pure (segments, (start, end))
      forAll genParam $ \(segments, (start, end)) -> do
        let result = RefUSegments.splice (start, end) segments
        widthOf result `shouldBe` end - start

  describe "normalize" $ do
    it "should result in valid RefUSegments" $ do
      property $ \segments -> do
        RefUSegments.isValid (RefUSegments.normalize segments) `shouldBe` True

  describe "fromSegment" $ do
    it "should result in valid RefUSegments" $ do
      let genParam = do
            slice <- arbitrary
            segment <- arbitrarySegmentOfSlice slice
            pure (slice, segment)
      forAll genParam $ \(slice, segment) -> do
        let segments = RefUSegments.fromSegment slice segment
        RefUSegments.isValid segments `shouldBe` True
