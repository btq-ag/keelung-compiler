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
  describe "SliceRelations.toAlignedSegmentPairsOfSelfRefs" $ do
    it "should handle this simple case correctly" $ do
      -- slice1     ├───────────╠═══════════╣─────┤
      -- slice2     ├─────╠═══════════╣───────────┤
      --        =>
      -- segments      1     2     3     4     5
      -- slice1     ├─────┼─────╠═════╬═════╣─────┤
      -- slice2     ├─────╠═════╬═════╣─────┼─────┤
      --
      -- segment1:   empty
      -- segment2:   child  of segment3
      -- segment3:   child  of segment4 and parent of segment2
      -- segment4:   parent of segment3
      -- segment5:   empty

      let slice1 = Slice (RefUI 25 0) 10 20
      let slice2 = Slice (RefUI 25 0) 5 15
      let segments = IntMap.fromList []

      SliceRelations.toAlignedSegmentPairsOfSelfRefs slice1 slice2 segments
        `shouldBe` [ ( Slice (RefUI 25 0) 0 5,
                       SliceLookup.Empty 5
                     ),
                     ( Slice (RefUI 25 0) 5 10,
                       SliceLookup.Empty 5
                     ),
                     ( Slice (RefUI 25 0) 10 15,
                       SliceLookup.Empty 5
                     ),
                     ( Slice (RefUI 25 0) 15 20,
                       SliceLookup.Empty 5
                     ),
                     ( Slice (RefUI 25 0) 20 25,
                       SliceLookup.Empty 5
                     )
                   ]

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

  -- describe "SliceRelations.relate" $ do
  --   -- it "should handle self references correctly" $ do
  --   --   let relations = SliceRelations.new
  --   --   let command = Relate (Slice (RefUI 40 0) 10 20) (Slice (RefUI 40 0) 15 25)
  --   --   let relations' = foldr execCommand relations [command]
  --   --   print relations'
  --   --   SliceRelations.collectFailure relations' `shouldBe` []

  --   -- it "should result in valid SliceRelations" $ do
  --   --   let relations = SliceRelations.new
  --   --   -- [(0,Empty[7]),
  --   --   --     (7,ChildOf[5] UI₃₉79 [12 ... 17)),
  --   --   --     (12,ChildOf[9] UI₃₉79 [17 ... 26)),
  --   --   --     (21,Parent[14] [(UI₃₉79,UI₃₉79 [7 ... 21))]),
  --   --   --     (26,Empty[13])]
  --   --   -- property $ \commands -> do
  --   --   --   let relations' = foldr execCommand relations (commands :: [Command])
  --   --   --   SliceRelations.collectFailure relations' `shouldBe` []
  --   --   -- property $ \(command1, command2, command3) -> do
  --   --   --   let relations' = foldr execCommand relations [command1, command2, command3]
  --   --   --   SliceRelations.collectFailure relations' `shouldBe` []
  --   --   let command2 = Relate (Slice (RefUI 39 79) 7 21) (Slice (RefUI 39 79) 12 26)
  --   --   let relations' = foldr execCommand relations [command2]
  --   --   SliceRelations.collectFailure relations' `shouldBe` []

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