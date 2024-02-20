-- | Polynomial of References and Slices
module Test.Data.PolyRS
  ( tests,
    run,
  )
where

import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Field (GF181)
import Test.Arbitrary ()
import Test.Hspec
import Test.QuickCheck

--------------------------------------------------------------------------------

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "PolyRS" $ do
  it "should be valid" $ do
    property $ \poly -> do
      PolyL.isValid (poly :: PolyL GF181) `shouldBe` True

-- describe "widthOf SliceLookup" $ do
--   it "should be the sum of all lengths of its segments" $ do
--     property $ \sliceLookup -> do
--       widthOf sliceLookup `shouldBe` sum (widthOf <$> IntMap.elems (lookupSegments sliceLookup))

-- describe "split & merge" $ do
--   it "should result in valid SliceLookups after normalization" $ do
--     let genParam = do
--           sliceLookup <- arbitrary
--           index <- chooseInt (0, widthOf sliceLookup - 1)
--           pure (sliceLookup, index)
--     forAll genParam $ \(sliceLookup, index) -> do
--       let (sliceLookup1, sliceLookup2) = SliceLookup.split index sliceLookup
--       SliceLookup.isValid sliceLookup1 `shouldBe` True
--       SliceLookup.isValid sliceLookup2 `shouldBe` True
--       SliceLookup.isValid (SliceLookup.normalize (sliceLookup1 <> sliceLookup2)) `shouldBe` True

--   it "should preserve lengths of segments (`(+) . widthOf . split = widthOf`)" $ do
--     let genParam = do
--           sliceLookup <- arbitrary
--           index <- chooseInt (0, widthOf sliceLookup - 1)
--           pure (sliceLookup, index)
--     forAll genParam $ \(sliceLookup, index) -> do
--       let (sliceLookup1, sliceLookup2) = SliceLookup.split index sliceLookup
--       widthOf sliceLookup1 + widthOf sliceLookup2 `shouldBe` widthOf sliceLookup

-- describe "splice" $ do
--   it "should result in a SliceLookup of the same width as of the interval" $ do
--     let genParam = do
--           sliceLookup <- arbitrary
--           let slice = lookupSlice sliceLookup
--           start <- chooseInt (sliceStart slice, (sliceEnd slice - 1) `max` sliceStart slice)
--           end <- chooseInt (start, (sliceEnd slice - 1) `max` sliceStart slice)
--           pure (sliceLookup, (start, end))
--     forAll genParam $ \(sliceLookup, (start, end)) -> do
--       let result = SliceLookup.splice (start, end) sliceLookup
--       widthOf result `shouldBe` end - start

-- describe "normalize" $ do
--   it "should be the coequalizer of `merge . split` and `id`" $ do
--     let genParam = do
--           sliceLookup <- arbitrary
--           index <- chooseInt (0, (widthOf sliceLookup - 1) `max` 0)
--           pure (sliceLookup, index)
--     forAll genParam $ \(sliceLookup, index) -> do
--       let (sliceLookup1, sliceLookup2) = SliceLookup.split index sliceLookup
--       SliceLookup.normalize (sliceLookup1 <> sliceLookup2) `shouldBe` SliceLookup.normalize sliceLookup

--   it "should result in valid SliceLookups" $ do
--     property $ \sliceLookup -> do
--       SliceLookup.isValid (SliceLookup.normalize sliceLookup) `shouldBe` True

-- describe "map" $ do
--   it "`map id = id`" $ do
--     property $ \sliceLookup -> do
--       let mapped = SliceLookup.map id sliceLookup
--       SliceLookup.isValid mapped `shouldBe` True
--       mapped `shouldBe` sliceLookup

-- describe "mapInterval" $ do
--   it "`mapInterval id = id`" $ do
--     let genParam = do
--           sliceLookup <- arbitrary
--           start <- chooseInt (0, widthOf sliceLookup - 1)
--           end <- chooseInt (start, widthOf sliceLookup)
--           pure (sliceLookup, (start, end))
--     forAll genParam $ \(sliceLookup, interval) -> do
--       let mapped = SliceLookup.mapInterval id interval sliceLookup
--       SliceLookup.isValid (SliceLookup.normalize mapped) `shouldBe` True
--       SliceLookup.normalize mapped `shouldBe` SliceLookup.normalize sliceLookup

-- describe "mapIntervalWithSlice" $ do
--   it "`mapIntervalWithSlice (\\_ x -> x) = id`" $ do
--     let genParam = do
--           sliceLookup <- arbitrary
--           start <- chooseInt (0, widthOf sliceLookup - 1)
--           end <- chooseInt (start, widthOf sliceLookup)
--           let slice = Slice (sliceRefU $ lookupSlice sliceLookup) start end
--           pure (sliceLookup, slice)
--     forAll genParam $ \(sliceLookup, slice) -> do
--       let mapped = SliceLookup.mapIntervalWithSlice (\_ x -> x) slice sliceLookup
--       SliceLookup.isValid (SliceLookup.normalize mapped) `shouldBe` True
--       SliceLookup.normalize mapped `shouldBe` SliceLookup.normalize sliceLookup

-- describe "pad" $ do
--   it "should result in valid SliceLookups" $ do
--     property $ \sliceLookup -> do
--       let padded = SliceLookup.pad sliceLookup
--       SliceLookup.isValid (SliceLookup.normalize padded) `shouldBe` True

-- describe "fromSegment" $ do
--   it "should result in valid SliceLookups" $ do
--     let genParam = do
--           slice <- arbitrary
--           segment <- arbitrarySegmentOfSlice slice
--           pure (slice, segment)
--     forAll genParam $ \(slice, segment) -> do
--       let sliceLookup = SliceLookup.fromSegment slice segment
--       SliceLookup.isValid sliceLookup `shouldBe` True
