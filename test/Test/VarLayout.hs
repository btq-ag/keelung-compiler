module Test.VarLayout (tests) where

import qualified Data.Sequence as Seq
import Keelung
import Keelung.Compiler
import Keelung.Syntax.VarCounters
import Test.Hspec

tests :: SpecWith ()
tests = do
  describe "Layout" $ do
    it "Num/Bool mixed 1" $
      let program = do
            num0 <- inputNum
            bool0 <- inputBool
            num1 <- inputNum
            bool1 <- inputBool
            return $ num0 + ToNum bool0 + num1 + ToNum bool1
          actual = asGF181N $ erasedVarCounters <$> erase program
          expected =
            Right $
              makeVarCounters
                181 -- width of GF(181)
                1 -- output
                2 -- Number
                2 -- Boolean
                0 -- intermediate
                [NumInput 0, BoolInput 0, NumInput 1, BoolInput 1]
                [] -- custom
       in actual `shouldBe` expected

    it "Num/Bool mixed 2" $
      let program = do
            num0 <- inputNum
            bool0 <- inputBool
            num1 <- inputNum
            bool1 <- inputBool
            return $ toArray [num0 + ToNum bool0, num1, ToNum bool1]
          actual = asGF181N $ erasedVarCounters <$> erase program
          expected =
            Right $
              makeVarCounters
                181 -- width of GF(181)
                3 -- output
                2 -- Number
                2 -- Boolean
                0 -- intermediate
                [NumInput 0, BoolInput 0, NumInput 1, BoolInput 1]
                [] -- custom
       in actual `shouldBe` expected

    it "Num/Bool mixed 3" $
      case asGF181N $ erasedVarCounters <$> erase example1 of
        Left err -> expectationFailure $ show err
        Right counters -> do
          -- check the formation of VarCounters
          counters
            `shouldBe` makeVarCounters
              181 -- width of GF(181)
              4 -- output
              5 -- Number
              4 -- Boolean
              0 -- intermediate
              [ NumInput 0,
                BoolInput 0,
                BoolInput 1,
                BoolInput 2,
                NumInput 1,
                NumInput 2,
                NumInput 3,
                NumInput 4,
                BoolInput 3
              ]
              [] -- custom

          -- check size of variable groups
          inputVarSize counters `shouldBe` (182 * 5 + 1 * 4)

          outputVars counters `shouldBe` [0 .. 3]
          inputVars counters `shouldBe` [4 .. 182 * 5 + 1 * 4 + 4 - 1]
          inputVarsRange counters `shouldBe` (4, 182 * 5 + 1 * 4 + 4)
          boolVarsRange counters `shouldBe` (9, 9 + 4 + 181 * 5)


          numInputVars counters `shouldBe` [4, 8, 9, 10, 11]

          getInputSequence counters
            `shouldBe` Seq.fromList
              [ NumInput 0,
                BoolInput 0,
                BoolInput 1,
                BoolInput 2,
                NumInput 1,
                NumInput 2,
                NumInput 3,
                NumInput 4,
                BoolInput 3
              ]

          getBitVar counters 3 0 `shouldBe` Nothing
          -- number
          getBitVar counters 4 0 `shouldBe` Just 13
          getBitVar counters 4 1 `shouldBe` Just 14
          getBitVar counters 4 180 `shouldBe` Just 193
          getBitVar counters 4 181 `shouldBe` Nothing
          -- booleans 
          getBitVar counters 5 0 `shouldBe` Nothing
          getBitVar counters 6 0 `shouldBe` Nothing
          getBitVar counters 7 0 `shouldBe` Nothing
          -- numbers 
          -- getBitVar counters 8 0 `shouldBe` Just 194

example1 :: Comp (Arr Number)
example1 = do
  num0 <- inputNum
  bools0 <- inputs 3
  nums1 <- inputs 4
  bool1 <- inputBool
  return $ toArray [num0, sum (fmap ToNum bools0), sum nums1, ToNum bool1]