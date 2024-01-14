module Test.Relations.Slice where

import Data.IntMap.Strict qualified as IntMap
import Keelung (widthOf)
import Keelung.Compiler.Relations.Slice (SliceRelations)
import Keelung.Compiler.Relations.Slice qualified as SliceRelations
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice (..))
import Keelung.Data.SliceLookup qualified as SliceLookup
import Test.Data.SliceLookup (arbitrarySliceOfWidth, arbitraryUOfWidth)
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
            value <- arbitraryUOfWidth (widthOf slice)
            pure (slice, value)
      forAll genParam $ \(slice, val) -> do
        let expected = SliceLookup.normalize $ SliceLookup.SliceLookup slice (IntMap.singleton (sliceStart slice) (SliceLookup.Constant val)) -- SliceLookup.mapInterval (const (SliceLookup.Constant val)) interval (SliceLookup.fromRefU ref)
        let relations' = SliceRelations.assign slice val relations
        let actual = SliceRelations.lookup slice relations'
        actual `shouldBe` expected

  describe "SliceRelations.relate" $ do
    it "should should result in valid SliceRelations" $ do
      let relations = SliceRelations.new
      -- property $ \commands -> do
      --   let relations' = foldr execCommand relations (commands :: [Command])
      --   SliceRelations.collectFailure relations' `shouldBe` []
      -- property $ \(command1, command2, command3) -> do
      --   let relations' = foldr execCommand relations [command1, command2, command3]
      --   SliceRelations.collectFailure relations' `shouldBe` []
      -- Relate UP₂₅33 [13 ... 15) UO₄₀12 [14 ... 16),Relate UI₃₅36 [6 ... 16) UI₂₈95 [0 ... 10),Relate UI₃₅36 [14 ... 24) UO₄₃9 [9 ... 19)
      -- let command1 = Relate (Slice (RefUP 25 33) 13 15) (Slice (RefUO 40 12) 14 16)
      let command2 = Relate (Slice (RefUI 35 36) 6 16) (Slice (RefUI 28 95) 0 10)
      let command3 = Relate (Slice (RefUI 35 36) 14 24) (Slice (RefUO 43 9) 9 19)
      let relations' = foldr execCommand relations [command2, command3]
      SliceRelations.collectFailure relations' `shouldBe` []

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