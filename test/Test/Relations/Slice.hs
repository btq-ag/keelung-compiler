module Test.Relations.Slice where

import Data.IntMap.Strict qualified as IntMap
import Keelung (widthOf)
import Keelung.Compiler.Relations.Slice (SliceRelations)
import Keelung.Compiler.Relations.Slice qualified as SliceRelations
import Keelung.Data.Reference (RefU (..))
import Keelung.Data.Slice (Slice (..))
import Keelung.Data.SliceLookup qualified as SliceLookup
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Test.Data.SliceLookup (arbitrarySliceOfWidth)
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "SliceRelations" $ do
  describe "SliceRelations.assign" $ do
    it "should return the assigned value on lookup" $ do
      let relations = SliceRelations.new
      let genParam = do
            slice <- arbitrary
            let width = widthOf slice
            val <- U.new width <$> chooseInteger (0, 2 ^ width - 1)
            pure (slice, val)
      forAll genParam $ \(slice, val) -> do
        let expected = SliceLookup.normalize $ SliceLookup.SliceLookup slice (IntMap.singleton (sliceStart slice) (SliceLookup.Constant val)) -- SliceLookup.mapInterval (const (SliceLookup.Constant val)) interval (SliceLookup.fromRefU ref)
        let relations' = SliceRelations.assign slice val relations
        let actual = SliceRelations.lookup slice relations'
        actual `shouldBe` expected

  describe "SliceRelations.relate" $ do
    it "should should result in valid SliceRelations" $ do
      let relations = SliceRelations.new
      property $ \commands -> do
        let relations' = foldr execCommand relations (commands :: [Command])
        SliceRelations.isValid relations' `shouldBe` True

--------------------------------------------------------------------------------

data Command = Relate Slice Slice deriving (Show)

instance Arbitrary Command where
  arbitrary = do
    width <- chooseInt (1, 16)
    Relate
      <$> arbitrarySliceOfWidth width
      <*> arbitrarySliceOfWidth width

execCommand :: Command -> SliceRelations -> SliceRelations
execCommand (Relate slice1 slice2) = SliceRelations.relate slice1 slice2

--------------------------------------------------------------------------------

-- instance Arbitrary RefU where
--   arbitrary = do
--     var <- chooseInt (0, 99)
--     constructor <- elements [RefUO, RefUI, RefUP, RefUX]
--     width <- chooseInt (1, 16)
--     pure $ constructor width var

-- instance Arbitrary Slice where
--   arbitrary = do
--     ref <- arbitrary
--     let width = widthOf ref
--     start <- chooseInt (0, width - 1)
--     end <- chooseInt (start, width)
--     pure $ Slice ref start end

-- instance Arbitrary U where
--   arbitrary = do
--     width <- chooseInt (1, 16)
--     value <- chooseInteger (0, 2 ^ width - 1)
--     pure $ U.new width value