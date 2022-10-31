module Test.VarLayout (tests) where

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
      let program = do
            num0 <- inputNum
            bools0 <- inputs 3
            nums1 <- inputs 4
            bool1 <- inputBool
            return $ toArray [num0, sum (fmap ToNum bools0), sum nums1, ToNum bool1]
          actual = asGF181N $ erasedVarCounters <$> erase program
          expected =
            Right $
              makeVarCounters
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
       in actual `shouldBe` expected
