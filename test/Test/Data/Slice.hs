module Test.Data.Slice (tests, run) where

import Data.IntMap qualified as IntMap
import Keelung (widthOf)
import Keelung.Data.Limb (Limb)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference (RefU (..))
import Keelung.Data.Slice (Segment (..), Slice (..))
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Test.Hspec
import Test.QuickCheck

--------------------------------------------------------------------------------

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Slice" $ do
  it "should be valid" $ do
    property $ \slice -> do
      Slice.isValid slice `shouldBe` True

  describe "widthOf Slice" $ do
    it "should be the sum of all lengths of its segments" $ do
      property $ \slice -> do
        widthOf slice `shouldBe` sum (widthOf <$> IntMap.elems (sliceSegments slice))

  describe "split & merge" $ do
    it "should result in valid Slices after normalization" $ do
      let genParam = do
            slice <- arbitrary
            index <- chooseInt (0, widthOf slice - 1)
            pure (slice, index)
      forAll genParam $ \(slice, index) -> do
        let (slice1, slice2) = Slice.split index slice
        Slice.isValid slice1 `shouldBe` True
        Slice.isValid slice2 `shouldBe` True
        Slice.isValid (Slice.normalize (slice1 <> slice2)) `shouldBe` True

    it "should preserve lengths of segments (`(+) . widthOf . split = widthOf`)" $ do
      let genParam = do
            slice <- arbitrary
            index <- chooseInt (0, widthOf slice - 1)
            pure (slice, index)
      forAll genParam $ \(slice, index) -> do
        let (slice1, slice2) = Slice.split index slice
        widthOf slice1 + widthOf slice2 `shouldBe` widthOf slice

  describe "normalize" $ do
    it "should be the coequalizer of `merge . split` and `id`" $ do
      let genParam = do
            slice <- arbitrary
            index <- chooseInt (0, (widthOf slice - 1) `max` 0)
            pure (slice, index)
      forAll genParam $ \(slice, index) -> do
        let (slice1, slice2) = Slice.split index slice
        Slice.normalize (slice1 <> slice2) `shouldBe` Slice.normalize slice

    it "should result in valid Slices" $ do
      property $ \slice -> do
        Slice.isValid (Slice.normalize slice) `shouldBe` True

  describe "map" $ do
    it "`map id = id`" $ do
      property $ \slice -> do
        let mapped = Slice.map id slice
        Slice.isValid mapped `shouldBe` True
        mapped `shouldBe` slice

  describe "mapInterval" $ do
    it "`mapInterval id = id`" $ do
      let genParam = do
            slice <- arbitrary
            start <- chooseInt (0, widthOf slice - 1)
            end <- chooseInt (start, widthOf slice)
            pure (slice, (start, end))
      forAll genParam $ \(slice, interval) -> do
        let mapped = Slice.mapInterval id interval slice
        Slice.isValid (Slice.normalize mapped) `shouldBe` True
        Slice.normalize mapped `shouldBe` Slice.normalize slice

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

instance Arbitrary Limb where
  arbitrary = do
    var <- arbitrary
    width <- chooseInt (1, widthOf var)
    offset <- chooseInt (0, widthOf var - width)
    sign <-
      oneof
        [ Left <$> arbitrary,
          Right <$> vectorOf width arbitrary
        ]
    pure $ Limb.new var width offset sign

instance Arbitrary Segment where
  arbitrary =
    oneof
      [ Constant <$> arbitrary,
        ChildOf <$> arbitrary,
        Parent <$> chooseInt (1, 16)
      ]

instance Arbitrary Slice where
  arbitrary = do
    offset <- chooseInt (0, 16)
    segments <- removeAdjectSameKind <$> arbitrary :: Gen [Segment]
    var <- arbitrary
    pure $ Slice.normalize $ Slice var offset (snd $ foldr (\segment (index, acc) -> (index + widthOf segment, IntMap.insert index segment acc)) (offset, mempty) segments)
    where
      sameKind :: Segment -> Segment -> Bool
      sameKind (Constant _) (Constant _) = True
      sameKind (ChildOf _) (ChildOf _) = True
      sameKind (Parent _) (Parent _) = True
      sameKind _ _ = False

      -- prevent segments of the same kind from being adjacent
      removeAdjectSameKind :: [Segment] -> [Segment]
      removeAdjectSameKind =
        foldr
          ( \segment acc -> case acc of
              [] -> [segment]
              (segment' : acc') -> if sameKind segment segment' then acc' else segment : acc
          )
          []