module Test.Data.SliceLookup (tests, run) where

import Data.IntMap qualified as IntMap
import Keelung (widthOf)
import Keelung.Data.Limb (Limb)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference (RefU (..))
import Keelung.Data.SliceLookup (Segment (..), SliceLookup (..))
import Keelung.Data.SliceLookup qualified as SliceLookup
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
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
        widthOf sliceLookup `shouldBe` sum (widthOf <$> IntMap.elems (sliceSegments sliceLookup))

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
    width <- chooseInt (0, widthOf var)
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

instance Arbitrary SliceLookup where
  arbitrary = do
    offset <- chooseInt (0, 16)
    segments <- removeAdjectSameKind <$> arbitrary :: Gen [Segment]
    var <- arbitrary
    pure $ SliceLookup.normalize $ SliceLookup var offset (snd $ foldr (\segment (index, acc) -> (index + widthOf segment, IntMap.insert index segment acc)) (offset, mempty) segments)
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