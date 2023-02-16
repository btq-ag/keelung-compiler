module Test.VarLayout (tests) where

import Keelung
import Keelung.Compiler
import Keelung.Compiler qualified as Compiler
import Keelung.Syntax.Counters
import Test.Hspec

tests :: SpecWith ()
tests = do
  describe "Variable indexing 0" $ do
    --
    --                F   B   BR  U
    --       output   3   0   0   0
    --        input   2   1   0   0
    -- intermediate   0   0   20  5
    --
    let counters =
          ( addCount OfPublicInput OfBoolean 1
              . addCount OfPublicInput OfField 2
              . addCount OfOutput OfField 3
              . addCount OfIntermediate (OfUInt 4) 5
          )
            mempty
    it "reindex" $ do
      reindex counters OfOutput OfField 0 `shouldBe` 0
      reindex counters OfOutput OfField 1 `shouldBe` 1
      reindex counters OfOutput OfField 2 `shouldBe` 2
      reindex counters OfPublicInput OfField 0 `shouldBe` 3
      reindex counters OfPublicInput OfField 1 `shouldBe` 4
      reindex counters OfPublicInput OfBoolean 0 `shouldBe` 5
      reindex counters OfIntermediate (OfUIntBinRep 4) 0 `shouldBe` 6
      reindex counters OfIntermediate (OfUIntBinRep 4) 1 `shouldBe` 10
      reindex counters OfIntermediate (OfUIntBinRep 4) 2 `shouldBe` 14
      reindex counters OfIntermediate (OfUIntBinRep 4) 3 `shouldBe` 18
      reindex counters OfIntermediate (OfUIntBinRep 4) 4 `shouldBe` 22
      reindex counters OfIntermediate (OfUInt 4) 0 `shouldBe` 26
      reindex counters OfIntermediate (OfUInt 4) 1 `shouldBe` 27
      reindex counters OfIntermediate (OfUInt 4) 2 `shouldBe` 28
      reindex counters OfIntermediate (OfUInt 4) 3 `shouldBe` 29

    it "getCount" $ do
      getCount OfOutput OfField counters `shouldBe` 3
      getCount OfOutput OfBoolean counters `shouldBe` 0
      getCount OfOutput (OfUIntBinRep 3) counters `shouldBe` 0
      getCount OfOutput (OfUIntBinRep 4) counters `shouldBe` 0
      getCount OfOutput (OfUIntBinRep 5) counters `shouldBe` 0
      getCount OfOutput (OfUInt 3) counters `shouldBe` 0
      getCount OfOutput (OfUInt 4) counters `shouldBe` 0
      getCount OfOutput (OfUInt 5) counters `shouldBe` 0
      getCount OfPublicInput OfField counters `shouldBe` 2
      getCount OfPublicInput OfBoolean counters `shouldBe` 1
      getCount OfPublicInput (OfUIntBinRep 3) counters `shouldBe` 0
      getCount OfPublicInput (OfUIntBinRep 4) counters `shouldBe` 0
      getCount OfPublicInput (OfUIntBinRep 5) counters `shouldBe` 0
      getCount OfPublicInput (OfUInt 3) counters `shouldBe` 0
      getCount OfPublicInput (OfUInt 4) counters `shouldBe` 0
      getCount OfPublicInput (OfUInt 5) counters `shouldBe` 0
      getCount OfIntermediate OfField counters `shouldBe` 0
      getCount OfIntermediate OfBoolean counters `shouldBe` 0
      getCount OfIntermediate (OfUIntBinRep 3) counters `shouldBe` 0
      getCount OfIntermediate (OfUIntBinRep 4) counters `shouldBe` 20
      getCount OfIntermediate (OfUIntBinRep 5) counters `shouldBe` 0
      getCount OfIntermediate (OfUInt 3) counters `shouldBe` 0
      getCount OfIntermediate (OfUInt 4) counters `shouldBe` 5
      getCount OfIntermediate (OfUInt 5) counters `shouldBe` 0

    it "getCountBySort" $ do
      getCountBySort OfOutput counters `shouldBe` 3
      getCountBySort OfPublicInput counters `shouldBe` 3
      getCountBySort OfIntermediate counters `shouldBe` 25

    it "getCountByType" $ do
      getCountByType OfField counters `shouldBe` 5
      getCountByType OfBoolean counters `shouldBe` 1
      getCountByType (OfUIntBinRep undefined) counters `shouldBe` 20
      getCountByType (OfUInt undefined) counters `shouldBe` 5

  describe "Variable indexing 1" $ do
    --
    --                F   B   BR  U
    --       output   0   6   0   0
    --        input   0   0   4   1
    -- intermediate   0   0   0   0
    --
    -- bitTestVarUI :: Comp (Arr Boolean)
    -- bitTestVarUI = do
    --   x <- inputUInt @4
    --   return $ toArray [x !!! (-1), x !!! 0, x !!! 1, x !!! 2, x !!! 3, x !!! 4]
    let counters =
          ( addCount OfPublicInput (OfUInt 4) 1
              . addCount OfOutput OfBoolean 6
          )
            mempty
    it "reindex" $ do
      reindex counters OfOutput OfBoolean 0 `shouldBe` 0
      reindex counters OfOutput OfBoolean 1 `shouldBe` 1
      reindex counters OfOutput OfBoolean 2 `shouldBe` 2
      reindex counters OfOutput OfBoolean 3 `shouldBe` 3
      reindex counters OfOutput OfBoolean 4 `shouldBe` 4
      reindex counters OfOutput OfBoolean 5 `shouldBe` 5
      reindex counters OfPublicInput (OfUIntBinRep 4) 0 `shouldBe` 6
      reindex counters OfPublicInput (OfUInt 4) 0 `shouldBe` 10

    it "getCount" $ do
      getCount OfOutput OfField counters `shouldBe` 0
      getCount OfOutput OfBoolean counters `shouldBe` 6
      getCount OfOutput (OfUIntBinRep 3) counters `shouldBe` 0
      getCount OfOutput (OfUIntBinRep 4) counters `shouldBe` 0
      getCount OfOutput (OfUIntBinRep 5) counters `shouldBe` 0
      getCount OfOutput (OfUInt 3) counters `shouldBe` 0
      getCount OfOutput (OfUInt 4) counters `shouldBe` 0
      getCount OfOutput (OfUInt 5) counters `shouldBe` 0
      getCount OfPublicInput OfField counters `shouldBe` 0
      getCount OfPublicInput OfBoolean counters `shouldBe` 0
      getCount OfPublicInput (OfUIntBinRep 3) counters `shouldBe` 0
      getCount OfPublicInput (OfUIntBinRep 4) counters `shouldBe` 4
      getCount OfPublicInput (OfUIntBinRep 5) counters `shouldBe` 0
      getCount OfPublicInput (OfUInt 3) counters `shouldBe` 0
      getCount OfPublicInput (OfUInt 4) counters `shouldBe` 1
      getCount OfPublicInput (OfUInt 5) counters `shouldBe` 0
      getCount OfIntermediate OfField counters `shouldBe` 0
      getCount OfIntermediate OfBoolean counters `shouldBe` 0
      getCount OfIntermediate (OfUIntBinRep 3) counters `shouldBe` 0
      getCount OfIntermediate (OfUIntBinRep 4) counters `shouldBe` 0
      getCount OfIntermediate (OfUIntBinRep 5) counters `shouldBe` 0
      getCount OfIntermediate (OfUInt 3) counters `shouldBe` 0
      getCount OfIntermediate (OfUInt 4) counters `shouldBe` 0
      getCount OfIntermediate (OfUInt 5) counters `shouldBe` 0

    it "getCountBySort" $ do
      getCountBySort OfOutput counters `shouldBe` 6
      getCountBySort OfPublicInput counters `shouldBe` 5
      getCountBySort OfIntermediate counters `shouldBe` 0

    it "getCountByType" $ do
      getCountByType OfField counters `shouldBe` 0
      getCountByType OfBoolean counters `shouldBe` 6
      getCountByType (OfUIntBinRep undefined) counters `shouldBe` 4
      getCountByType (OfUInt undefined) counters `shouldBe` 1

  describe "Variable indexing 2" $ do
    --
    --                F   B   BR  U
    --       output   0   0   4   1
    --        input   0   0   8   2
    -- intermediate   0   0   4   1
    --
    let counters =
          ( addCount OfOutput (OfUInt 4) 1
              . addCount OfPublicInput (OfUInt 4) 2
              . addCount OfIntermediate (OfUInt 4) 1
          )
            mempty
    it "reindex" $ do
      reindex counters OfOutput (OfUIntBinRep 4) 0 `shouldBe` 0
      reindex counters OfOutput (OfUInt 4) 0 `shouldBe` 4
      reindex counters OfPublicInput (OfUIntBinRep 4) 0 `shouldBe` 5
      reindex counters OfPublicInput (OfUIntBinRep 4) 1 `shouldBe` 9
      reindex counters OfPublicInput (OfUInt 4) 0 `shouldBe` 13
      reindex counters OfPublicInput (OfUInt 4) 1 `shouldBe` 14
      reindex counters OfIntermediate (OfUIntBinRep 4) 0 `shouldBe` 15
      reindex counters OfIntermediate (OfUInt 4) 0 `shouldBe` 19

    it "getCountBySort" $ do
      getCountBySort OfOutput counters `shouldBe` 5
      getCountBySort OfPublicInput counters `shouldBe` 10
      getCountBySort OfIntermediate counters `shouldBe` 5

    it "getCountByType" $ do
      getCountByType OfField counters `shouldBe` 0
      getCountByType OfBoolean counters `shouldBe` 0
      getCountByType (OfUIntBinRep undefined) counters `shouldBe` 16
      getCountByType (OfUInt undefined) counters `shouldBe` 4

  describe "Layout 0" $ do
    --                F   B   BR  U
    --       output   1   0   0   0
    --        input   3   0   0   0
    -- intermediate   0   0   0   0
    let program = do
          x <- inputField Public
          y <- inputField Public
          z <- inputField Public
          return $ x + y + z
    case asGF181 $ csCounters <$> Compiler.compile program of
      Left err -> it "Erasure failure" $ expectationFailure (show err)
      Right counters -> do
        it "reindex" $ do
          reindex counters OfOutput OfField 0 `shouldBe` 0
          reindex counters OfPublicInput OfField 0 `shouldBe` 1
          reindex counters OfPublicInput OfField 1 `shouldBe` 2
          reindex counters OfPublicInput OfField 2 `shouldBe` 3

  describe "Layout 1" $ do
    --                F   B   BR  U
    --       output   1   0   0   0
    --        input   1   1   0   0
    -- intermediate   0   0   0   0
    let program = do
          x <- inputField Public
          y <- inputBool Public
          return $ cond y x 0
    case asGF181 $ csCounters <$> Compiler.compile program of
      Left err -> it "Erasure failure" $ expectationFailure (show err)
      Right counters -> do
        it "reindex" $ do
          reindex counters OfOutput OfField 0 `shouldBe` 0
          reindex counters OfPublicInput OfField 0 `shouldBe` 1
          reindex counters OfPublicInput OfBoolean 0 `shouldBe` 2
