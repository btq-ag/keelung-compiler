{-# LANGUAGE FlexibleInstances #-}

module Test.Data.SliceLookup
  ( tests,
    run,
    arbitraryUOfWidth,
    arbitrarySliceOfWidth,
    arbitrarySegmentOfSlice,
    arbitraryRefUOfWidth,
  )
where

import Data.IntMap qualified as IntMap
import Data.Map.Strict qualified as Map
import Keelung (widthOf)
import Keelung.Data.Reference (RefU (..))
import Keelung.Data.Slice (Slice (..))
import Keelung.Data.SliceLookup (Segment (..), SliceLookup (..))
import Keelung.Data.SliceLookup qualified as SliceLookup
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Keelung.Syntax (Width)
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
        let (sliceLookup1, sliceLookup2) = SliceLookup.split index sliceLookup
        SliceLookup.isValid sliceLookup1 `shouldBe` True
        SliceLookup.isValid sliceLookup2 `shouldBe` True
        SliceLookup.isValid (SliceLookup.normalize (sliceLookup1 <> sliceLookup2)) `shouldBe` True

    it "should preserve lengths of segments (`(+) . widthOf . split = widthOf`)" $ do
      let genParam = do
            sliceLookup <- arbitrary
            index <- chooseInt (0, widthOf sliceLookup - 1)
            pure (sliceLookup, index)
      forAll genParam $ \(sliceLookup, index) -> do
        let (sliceLookup1, sliceLookup2) = SliceLookup.split index sliceLookup
        widthOf sliceLookup1 + widthOf sliceLookup2 `shouldBe` widthOf sliceLookup

  describe "normalize" $ do
    it "should be the coequalizer of `merge . split` and `id`" $ do
      let genParam = do
            sliceLookup <- arbitrary
            index <- chooseInt (0, (widthOf sliceLookup - 1) `max` 0)
            pure (sliceLookup, index)
      forAll genParam $ \(sliceLookup, index) -> do
        let (sliceLookup1, sliceLookup2) = SliceLookup.split index sliceLookup
        SliceLookup.normalize (sliceLookup1 <> sliceLookup2) `shouldBe` SliceLookup.normalize sliceLookup

    it "should result in valid SliceLookups" $ do
      property $ \sliceLookup -> do
        SliceLookup.isValid (SliceLookup.normalize sliceLookup) `shouldBe` True

  describe "map" $ do
    it "`map id = id`" $ do
      property $ \sliceLookup -> do
        let mapped = SliceLookup.map id sliceLookup
        SliceLookup.isValid mapped `shouldBe` True
        mapped `shouldBe` sliceLookup

  describe "mapInterval" $ do
    it "`mapInterval id = id`" $ do
      let genParam = do
            sliceLookup <- arbitrary
            start <- chooseInt (0, widthOf sliceLookup - 1)
            end <- chooseInt (start, widthOf sliceLookup)
            pure (sliceLookup, (start, end))
      forAll genParam $ \(sliceLookup, interval) -> do
        let mapped = SliceLookup.mapInterval id interval sliceLookup
        SliceLookup.isValid (SliceLookup.normalize mapped) `shouldBe` True
        SliceLookup.normalize mapped `shouldBe` SliceLookup.normalize sliceLookup

  describe "mapIntervalWithSlice" $ do
    it "`mapIntervalWithSlice (\\_ x -> x) = id`" $ do
      let genParam = do
            sliceLookup <- arbitrary
            start <- chooseInt (0, widthOf sliceLookup - 1)
            end <- chooseInt (start, widthOf sliceLookup)
            let slice = Slice (sliceRefU $ lookupSlice sliceLookup) start end
            pure (sliceLookup, slice)
      forAll genParam $ \(sliceLookup, slice) -> do
        let mapped = SliceLookup.mapIntervalWithSlice (\_ x -> x) slice sliceLookup
        SliceLookup.isValid (SliceLookup.normalize mapped) `shouldBe` True
        SliceLookup.normalize mapped `shouldBe` SliceLookup.normalize sliceLookup

  describe "pad" $ do
    it "should result in valid SliceLookups" $ do
      property $ \sliceLookup -> do
        let padded = SliceLookup.pad sliceLookup
        SliceLookup.isValid (SliceLookup.normalize padded) `shouldBe` True

  describe "fromSegment" $ do
    it "should result in valid SliceLookups" $ do
      let genParam = do
            slice <- arbitrary
            segment <- arbitrarySegmentOfSlice slice
            pure (slice, segment)
      forAll genParam $ \(slice, segment) -> do
        let sliceLookup = SliceLookup.fromSegment slice segment
        SliceLookup.isValid sliceLookup `shouldBe` True

--------------------------------------------------------------------------------

instance Arbitrary RefU where
  arbitrary = arbitraryRefUOfWidth 1 16

arbitraryRefUOfWidth :: Width -> Width -> Gen RefU
arbitraryRefUOfWidth widthLowerBound widthUpperBound = do
  width <- chooseInt (widthLowerBound, widthUpperBound)
  var <- chooseInt (0, 99)
  constructor <- elements [RefUO, RefUI, RefUP, RefUX]
  pure $ constructor width var

instance Arbitrary U where
  arbitrary = chooseInt (1, 16) >>= arbitraryUOfWidth

arbitraryUOfWidth :: Width -> Gen U
arbitraryUOfWidth width = do
  value <- chooseInteger (0, 2 ^ width - 1)
  pure $ U.new width value

instance Arbitrary Segment where
  arbitrary = arbitrary >>= arbitrarySegmentOfSlice

arbitrarySegmentOfSlice :: Slice -> Gen Segment
arbitrarySegmentOfSlice (Slice _ start end) =
  let width = end - start
   in oneof
        [ Constant <$> arbitraryUOfWidth width,
          ChildOf <$> arbitrarySliceOfWidth width,
          do
            childrenCount <- chooseInt (1, 16)
            children <- vectorOf childrenCount $ arbitrarySliceOfWidth width
            pure $ Parent width (Map.fromList (map (\child -> (sliceRefU child, child)) children)) mempty mempty
        ]

instance Arbitrary Slice where
  arbitrary = chooseInt (1, 16) >>= arbitrarySliceOfWidth

arbitrarySliceOfWidth :: Width -> Gen Slice
arbitrarySliceOfWidth width = do
  -- choose the starting offset of the slice first
  start <- chooseInt (0, 16)
  let end = start + width
  refUWidth <- chooseInt (end, end + 16)
  ref <- arbitraryRefUOfWidth refUWidth (refUWidth + 16)
  pure $ Slice ref start end

instance Arbitrary SliceLookup where
  arbitrary = do
    start <- chooseInt (0, 16)
    segments <- removeAdjectSameKind <$> arbitrary
    let width = sum (map widthOf segments)
    var <- arbitraryRefUOfWidth width (width + 16)
    pure $
      SliceLookup.normalize $
        SliceLookup
          (Slice var start (start + width))
          (snd $ foldr (\segment (index, acc) -> (index + widthOf segment, IntMap.insert index segment acc)) (start, mempty) segments)
    where
      -- prevent segments of the same kind from being adjacent
      removeAdjectSameKind :: [Segment] -> [Segment]
      removeAdjectSameKind =
        foldr
          ( \segment acc -> case acc of
              [] -> [segment]
              (segment' : acc') -> if SliceLookup.sameKindOfSegment segment segment' then acc' else segment : acc
          )
          []