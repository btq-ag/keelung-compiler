module Test.Relations.Slice where

import Data.IntMap.Strict qualified as IntMap
import Keelung (widthOf)
import Keelung.Compiler.Relations.Slice (SliceRelations)
import Keelung.Compiler.Relations.Slice qualified as SliceRelations
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice (..))
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.SliceLookup qualified as SliceLookup
import Test.Data.SliceLookup (arbitrarySliceOfWidth, arbitraryUOfWidth)
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "SliceRelations" $ do
  describe "SliceRelations.toAlignedSegmentPairsOverlapping" $ do
    it "should handle this simple case correctly" $ do
      -- slice1     ├───────────╠═════════════════╣─────┤
      -- slice2     ├─────╠═════════════════╣───────────┤
      --        =>
      --                              ┌──w──┬──w──┐ 
      -- result     ├─────╠═══════════╬═════╬═════╣─────┤
      --                              ↑
      --                             new
      let slice1 = Slice (RefUI 60 0) 20 50
      let slice2 = Slice (RefUI 60 0) 10 40

      SliceRelations.toAlignedSegmentPairsOverlapping2 slice1 slice2
        `shouldBe` [ ( Slice (RefUI 60 0) 0 10,
                       SliceLookup.Empty 10
                     ),
                     ( Slice (RefUI 60 0) 10 30,
                       SliceLookup.Empty 20
                     ),
                     ( Slice (RefUI 60 0) 30 40,
                       SliceLookup.Empty 10
                     ),
                     ( Slice (RefUI 60 0) 40 50,
                       SliceLookup.Empty 10
                     ),
                     ( Slice (RefUI 60 0) 50 60,
                       SliceLookup.Empty 10
                     )
                   ]

    -- it "should handle this simple case correctly" $ do
    --   -- slice1     ├───────────╠═══════════╣─────┤
    --   -- slice2     ├─────╠═══════════╣───────────┤
    --   --        =>
    --   -- segments      1     2     3     4     5
    --   -- slice1     ├─────┼─────╠═════╬═════╣─────┤
    --   -- slice2     ├─────╠═════╬═════╣─────┼─────┤
    --   --
    --   -- segment1:   empty
    --   -- segment2:   child  of segment3
    --   -- segment3:   child  of segment4 and parent of segment2
    --   -- segment4:   parent of segment3
    --   -- segment5:   empty

    --   let slice1 = Slice (RefUI 25 0) 10 20
    --   let slice2 = Slice (RefUI 25 0) 5 15

    --   SliceRelations.toAlignedSegmentPairsOverlapping slice1 slice2
    --     `shouldBe` [ ( Slice (RefUI 25 0) 0 5,
    --                    SliceLookup.Empty 5
    --                  ),
    --                  ( Slice (RefUI 25 0) 5 10,
    --                    SliceLookup.Empty 5
    --                  ),
    --                  ( Slice (RefUI 25 0) 10 15,
    --                    SliceLookup.Empty 5
    --                  ),
    --                  ( Slice (RefUI 25 0) 15 20,
    --                    SliceLookup.Empty 5
    --                  ),
    --                  ( Slice (RefUI 25 0) 20 25,
    --                    SliceLookup.Empty 5
    --                  )
    --                ]

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
    it "should result in valid SliceRelations, when the related slices are non-overlapping" $ do
      let relations = SliceRelations.new
      forAll arbitraryNonOverlappingCommands $ \commands -> do
        let relations' = foldr execCommand relations commands
        SliceRelations.collectFailure relations' `shouldBe` []

    it "should handle this simple case correctly" $ do
      let relations = SliceRelations.new
      let commands =
            [ Relate (Slice (RefUO 30 0) 10 30) (Slice (RefUO 30 0) 0 20)
            ]
      let relations' = foldr execCommand relations commands
      print relations'
      SliceRelations.collectFailure relations' `shouldBe` []




-- describe "SliceRelations.toAlignedSegmentPairsOfSelfRefs" $ do
--   it "should handle this simple case correctly" $ do
--     -- slice1     ╠═════1═════╣─────┤
--     -- slice2     ├─────╠═════2═════╣

--     let slice1 = Slice (RefUO 30 1) 0 20
--     let slice2 = Slice (RefUO 30 2) 10 30

--     let segments = IntMap.fromList []

--     SliceRelations.toAlignedSegmentPairsOfSelfRefs slice1 slice2 segments
--       `shouldBe` [ ( Slice (RefUO 30 1) 0 20,
--                      SliceLookup.Empty 20
--                    ),
--                    ( Slice (RefUO 30 1) 20 30,
--                      SliceLookup.Empty 10
--                    ),
--                    )
--                  ]
-- it "should handle this simple case correctly" $ do
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

-- let slice1 = Slice (RefUI 25 0) 10 20
-- let slice2 = Slice (RefUI 25 0) 5 15
-- let segments = IntMap.fromList []

-- SliceRelations.toAlignedSegmentPairsOfSelfRefs slice1 slice2 segments
--   `shouldBe` [ ( Slice (RefUI 25 0) 0 5,
--                  SliceLookup.Empty 5
--                ),
--                ( Slice (RefUI 25 0) 5 10,
--                  SliceLookup.Empty 5
--                ),
--                ( Slice (RefUI 25 0) 10 15,
--                  SliceLookup.Empty 5
--                ),
--                ( Slice (RefUI 25 0) 15 20,
--                  SliceLookup.Empty 5
--                ),
--                ( Slice (RefUI 25 0) 20 25,
--                  SliceLookup.Empty 5
--                )
--              ]

--   let relations = SliceRelations.new
--   let command = Relate (Slice (RefUI 25 0) 10 20) (Slice (RefUI 25 0) 5 15)
--   let relations' = foldr execCommand relations [command]
--   -- print relations'
--   let expected =
--         SliceLookup.SliceLookup (Slice (RefUI 25 0) 0 25) $
--           IntMap.fromList
--             [
--               (0, SliceLookup.Empty 5)
--             ]
--   let actual = SliceRelations.lookup (Slice (RefUI 25 0) 0 25) relations'
--   actual `shouldBe` expected

-- it "should result in valid SliceRelations, when the related slices are non-overlapping" $ do
--   let relations = SliceRelations.new
--   let commands =
--         [ Relate (Slice (RefUP 30 0) 0 10) (Slice (RefUO 30 99) 8 14),
--           Relate (Slice (RefUX 30 1) 0 10) (Slice (RefUO 30 99) 13 23),
--           Relate (Slice (RefUP 30 2) 0 10) (Slice (RefUO 30 99) 6 16)
--         ]

--   let relations' = foldr execCommand relations commands
--   print relations'
--   SliceRelations.collectFailure relations' `shouldBe` []

-- it "should result in valid SliceRelations, when the related slices are non-overlapping" $ do
--   let relations = SliceRelations.new
--   let commands =
--         [ Relate (Slice (RefUP 30 0) 0 10) (Slice (RefUO 30 99) 0 10),
--           Relate (Slice (RefUX 30 1) 0 10) (Slice (RefUO 30 99) 10 20),
--           Relate (Slice (RefUP 30 2) 0 10) (Slice (RefUO 30 99) 20 30)
--         ]

--   let relations' = foldr execCommand relations commands
--   SliceRelations.collectFailure relations' `shouldBe` []

--------------------------------------------------------------------------------

data Command = Relate Slice Slice deriving (Show)

arbitraryCommandOfOverlapping :: Bool -> Gen Command
arbitraryCommandOfOverlapping overlap = do
  width <- chooseInt (1, 16)
  slice1 <- arbitrarySliceOfWidth width
  slice2 <-
    arbitrarySliceOfWidth width `suchThat` \slice2 ->
      if overlap
        then Slice.overlaps slice1 slice2
        else not (Slice.overlaps slice1 slice2)
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

-- arbitraryOverlappingCommands :: Gen [Command]
-- arbitraryOverlappingCommands = liseOf(arbitraryCommandOfOverlapping True)

instance Arbitrary Command where
  arbitrary = arbitraryCommandOfOverlapping True

execCommand :: Command -> SliceRelations -> SliceRelations
execCommand (Relate slice1 slice2) = SliceRelations.relate slice1 slice2