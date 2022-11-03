{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.VarLayout (tests) where

import qualified Data.Sequence as Seq
import Keelung
import Keelung.Compiler
import Keelung.Syntax.VarCounters
import Test.Hspec

tests :: SpecWith ()
tests = do
  describe "Layout" $ do
    case asGF181N $ erasedVarCounters <$> erase example1 of
      Left err -> it "Erasure of example1" $ expectationFailure (show err)
      Right counters -> do
        it "VarCounters constuction" $ do
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
        it "Size of variable groups" $ do
          inputVarSize counters `shouldBe` (182 * 5 + 1 * 4)
          outputVars counters `shouldBe` [0 .. 3]
          inputVars counters `shouldBe` [4 .. 182 * 5 + 1 * 4 + 4 - 1]
          inputVarsRange counters `shouldBe` (4, 182 * 5 + 1 * 4 + 4)
          boolVarsRange counters `shouldBe` (9, 9 + 4 + 181 * 5)
          blendedNumInputVars counters `shouldBe` [4, 8, 9, 10, 11]
        it "Input sequence" $ do
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

        it "Bit tests" $ do
          getBitVar counters 3 0 `shouldBe` Nothing
          -- number
          map (getBitVar counters 4) [0 .. 180] `shouldBe` map Just [13 .. 193]
          -- booleans
          getBitVar counters 5 0 `shouldBe` Nothing
          getBitVar counters 6 0 `shouldBe` Nothing
          getBitVar counters 7 0 `shouldBe` Nothing
          -- numbers
          map (getBitVar counters 8) [0 .. 180] `shouldBe` map Just [194 .. 374]

    case asGF181N $ erasedVarCounters <$> erase example2 of
        Left err -> it "Erasure of example2" $ expectationFailure (show err)
        Right counters -> do
          it "VarCounters constuction" $ do
            -- check the formation of VarCounters
            counters
              `shouldBe` makeVarCounters
                181 -- width of GF(181)
                3 -- output
                1 -- Number
                1 -- Boolean
                0 -- intermediate
                [ NumInput 0,
                  CustomInput 4 0,
                  BoolInput 0
                ]
                [(4, 1)] -- custom
          it "Size of variable groups" $ do
            inputVarSize counters `shouldBe` (3 + 181 + 4)
            totalCustomInputSize counters `shouldBe` 1
            customBinRepVarSize counters `shouldBe` 4 
            totalBoolVarSize counters `shouldBe` 186

          it "Bit tests" $ do
            getBitVar counters 2 0 `shouldBe` Nothing
            -- number
            map (getBitVar counters 3) [0 .. 180] `shouldBe` map Just [6 .. 186]
            -- 4-bit unsigned integer 
            map (getBitVar counters 4) [0 .. 3] `shouldBe` map Just [187 .. 190]
            -- getBitVar counters 4 4  `shouldBe` Nothing


    case asGF181N $ erasedVarCounters <$> erase example3 of
        Left err -> it "Erasure of example3" $ expectationFailure (show err)
        Right counters -> do
          it "VarCounters constuction" $ do
            -- check the formation of VarCounters
            counters
              `shouldBe` makeVarCounters
                181 -- width of GF(181)
                4 -- output
                0 -- Number
                0 -- Boolean
                0 -- intermediate
                [ CustomInput 4 0
                ]
                [(4, 1)] -- custom
          it "Size of variable groups" $ do
            inputVarSize counters `shouldBe` 5
            totalCustomInputSize counters `shouldBe` 1
            customBinRepVarSize counters `shouldBe` 4
            totalBoolVarSize counters `shouldBe` 4
            boolVarsRange counters `shouldBe` (5, 9)

example1 :: Comp (Arr Number)
example1 = do
  num0 <- inputNum
  bools0 <- inputs 3
  nums1 <- inputs 4
  bool1 <- inputBool
  return $ toArray [num0, sum (fmap FromBool bools0), sum nums1, FromBool bool1]

example2 :: Comp (Arr Number)
example2 = do
  num0 <- inputNum
  uint0 <- inputUInt @4
  bool0 <- inputBool
  return $ toArray [num0, FromBool (uint0 !!! 0), FromBool bool0]

example3 :: Comp (Arr Boolean)
example3 = do
  x <- inputUInt @4
  return $ toArray [x !!! 0, x !!! 1, x !!! 2, x !!! 3]
