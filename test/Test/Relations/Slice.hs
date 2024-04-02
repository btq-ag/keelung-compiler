module Test.Relations.Slice where

import Data.IntMap.Strict qualified as IntMap
import Keelung (widthOf)
import Keelung.Compiler.Relations.Slice (SliceRelations)
import Keelung.Compiler.Relations.Slice qualified as SliceRelations
import Keelung.Data.Reference
import Keelung.Data.Segment qualified as Segment
import Keelung.Data.Slice (Slice (..))
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.RefUSegments qualified as RefUSegments
import Test.Arbitrary
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
            ref <- arbitrary
            value <- arbitraryUOfWidth (widthOf ref)
            pure (ref, value)
      forAll genParam $ \(ref, val) -> do
        let expected = RefUSegments.normalize $ RefUSegments.RefUSegments ref (IntMap.singleton 0 (Segment.Constant val))
        let relations' = SliceRelations.assign (Slice.fromRefU ref) val relations
        let actual = SliceRelations.lookup (Slice.fromRefU ref) relations'
        actual `shouldBe` expected

  describe "SliceRelations.lookup" $ do
    it "the length of input `Slice` should match the length of the output `RefUSegments" $ do
      let relations = SliceRelations.new
      property $ \(commands, slice) -> do
        let relations' = foldr execCommand relations (commands :: [Command])
        let result = SliceRelations.lookup slice relations'
        widthOf slice `shouldBe` widthOf result

  describe "SliceRelations.relate" $ do
    it "should result in valid SliceRelations, when the related slices are non-overlapping" $ do
      let relations = SliceRelations.new
      forAll arbitraryNonOverlappingCommands $ \commands -> do
        let relations' = foldr execCommand relations commands
        SliceRelations.validate relations' `shouldBe` []

    it "should result in valid SliceRelations" $ do
      let relations = SliceRelations.new
      property $ \commands -> do
        let relations' = foldr execCommand relations (commands :: [Command])
        SliceRelations.validate relations' `shouldBe` []

    it "should handle this simple case correctly 1" $ do
      let relations = SliceRelations.new
      let commands =
            [ Relate (Slice (RefUO 30 0) 10 30) (Slice (RefUO 30 0) 0 20)
            ]
      let relations' = foldr execCommand relations commands
      SliceRelations.validate relations' `shouldBe` []

    it "should handle this simple case correctly 2" $ do
      -- RefUO 50 0     ├───────────╠═══════════╣─────┤
      -- RefUO 50 0     ├─────╠═══════════╣───────────┤
      -- RefUX 30 1                 ╠═══════════╣
      let relations = SliceRelations.new
      let commands =
            [ Relate (Slice (RefUO 50 0) 20 40) (Slice (RefUO 50 0) 10 30),
              Relate (Slice (RefUO 50 0) 20 40) (Slice (RefUX 30 1) 0 20)
            ]
      let relations' = foldl (flip execCommand) relations commands
      SliceRelations.validate relations' `shouldBe` []

    it "should handle this simple case correctly 3" $ do
      -- RefUO 50 0     ├───────────╠═══════════╣─────┤
      -- RefUO 50 0     ├─────╠═══════════╣───────────┤
      -- RefUO 50 0     ├─────────────────╠═══════════╣
      let relations = SliceRelations.new
      let commands =
            [ Relate (Slice (RefUO 50 0) 20 40) (Slice (RefUO 50 0) 10 30),
              Relate (Slice (RefUO 50 0) 20 40) (Slice (RefUO 50 0) 30 50)
            ]
      let relations' = foldl (flip execCommand) relations commands
      SliceRelations.validate relations' `shouldBe` []

--------------------------------------------------------------------------------

data Command = Relate Slice Slice deriving (Show)

arbitraryCommandOfOverlapping :: Bool -> Gen Command
arbitraryCommandOfOverlapping canOverlap = do
  width <- chooseInt (1, 16)
  slice1 <- arbitrarySliceOfWidth width
  slice2 <-
    arbitrarySliceOfWidth width `suchThat` \slice2 -> canOverlap || not (Slice.overlaps slice1 slice2)
  pure $ Relate slice1 slice2

arbitraryNonOverlappingCommands :: Gen [Command]
arbitraryNonOverlappingCommands = do
  numOfCommands <- chooseInt (0, 20)
  gen numOfCommands []
  where
    overlaps :: Command -> Command -> Bool
    overlaps (Relate x y) (Relate v w) = x `Slice.overlaps` v || x `Slice.overlaps` w || y `Slice.overlaps` v || y `Slice.overlaps` w

    gen :: Int -> [Command] -> Gen [Command]
    gen numOfCommands accumulated =
      if length accumulated >= numOfCommands
        then pure accumulated
        else do
          command <- arbitraryCommandOfOverlapping False `suchThat` \command -> not $ any (overlaps command) accumulated
          gen numOfCommands (command : accumulated)

instance Arbitrary Command where
  arbitrary = arbitraryCommandOfOverlapping True

execCommand :: Command -> SliceRelations -> SliceRelations
execCommand (Relate slice1 slice2) = SliceRelations.relate slice1 slice2