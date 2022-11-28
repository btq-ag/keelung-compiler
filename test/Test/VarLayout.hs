module Test.VarLayout (tests) where

import Keelung
import Keelung.Compiler
import qualified Keelung.Compiler as Compiler
import Keelung.Syntax.Counters
import Test.Hspec

tests :: SpecWith ()
tests = do
  describe "Variable indexing" $ do
    --
    --                F   B   BR  U
    --       output   3   0   0   0
    --        input   2   1   0   0
    -- intermediate   0   0   20  4
    --
    let counters =
          ( setCount OfInput OfBoolean 1
              . setCount OfInput OfField 2
              . setCount OfOutput OfField 3
              . setCount OfIntermediate (OfUIntBinRep 4) 5
              . setCount OfIntermediate (OfUInt 4) 5
          )
            mempty
    it "reindex 0" $ do
      reindex counters OfOutput OfField 0 `shouldBe` 0
      reindex counters OfOutput OfField 1 `shouldBe` 1
      reindex counters OfOutput OfField 2 `shouldBe` 2
      reindex counters OfInput OfField 0 `shouldBe` 3
      reindex counters OfInput OfField 1 `shouldBe` 4
      reindex counters OfInput OfBoolean 0 `shouldBe` 5
      reindex counters OfIntermediate (OfUIntBinRep 4) 0 `shouldBe` 6
      reindex counters OfIntermediate (OfUIntBinRep 4) 1 `shouldBe` 7
      reindex counters OfIntermediate (OfUIntBinRep 4) 2 `shouldBe` 8
      reindex counters OfIntermediate (OfUIntBinRep 4) 3 `shouldBe` 9
      reindex counters OfIntermediate (OfUIntBinRep 4) 4 `shouldBe` 10
      reindex counters OfIntermediate (OfUInt 4) 0 `shouldBe` 26
      reindex counters OfIntermediate (OfUInt 4) 1 `shouldBe` 27
      reindex counters OfIntermediate (OfUInt 4) 2 `shouldBe` 28
      reindex counters OfIntermediate (OfUInt 4) 3 `shouldBe` 29

  describe "Layout 0" $ do
    --                F   B   BR  U
    --       output   1   0   0   0
    --        input   3   0   0   0
    -- intermediate   0   0   0   0
    let program = do
          x <- inputNum
          y <- inputNum
          z <- inputNum
          return $ x + y + z
    case asGF181N $ csCounters <$> Compiler.compile program of
      Left err -> it "Erasure failure" $ expectationFailure (show err)
      Right counters -> do
        it "reindex" $ do
          reindex counters OfOutput OfField 0 `shouldBe` 0
          reindex counters OfInput OfField 0 `shouldBe` 1
          reindex counters OfInput OfField 1 `shouldBe` 2
          reindex counters OfInput OfField 2 `shouldBe` 3

  describe "Layout 1" $ do
    --                F   B   BR  U
    --       output   1   0   0   0
    --        input   1   1   0   0
    -- intermediate   0   0   0   0
    let program = do
          x <- inputNum
          y <- inputBool
          return $ cond y x 0
    case asGF181N $ csCounters <$> Compiler.compile program of
      Left err -> it "Erasure failure" $ expectationFailure (show err)
      Right counters -> do
        it "reindex" $ do
          reindex counters OfOutput OfField 0 `shouldBe` 0
          reindex counters OfInput OfField 0 `shouldBe` 1
          reindex counters OfInput OfBoolean 0 `shouldBe` 2
