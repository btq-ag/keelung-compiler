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
          numInputVarsRange counters `shouldBe` (4, 9)
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

        it "Index of binary representation" $ do
          lookupBinRepStart counters 3 `shouldBe` Nothing
          -- number
          lookupBinRepStart counters 4 `shouldBe` Just 13
          lookupBinRepStart counters 5 `shouldBe` Just 194
          lookupBinRepStart counters 6 `shouldBe` Just 375
          lookupBinRepStart counters 7 `shouldBe` Just 556
          lookupBinRepStart counters 8 `shouldBe` Just 737
          -- booleans
          lookupBinRepStart counters 9 `shouldBe` Nothing

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

          it "Index of binary representation" $ do
            lookupBinRepStart counters 2 `shouldBe` Nothing
            -- number
            lookupBinRepStart counters 3 `shouldBe` Just 6
            -- 4-bit unsigned integer 
            lookupBinRepStart counters 4 `shouldBe` Just 187


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

    case asGF181N $ erasedVarCounters <$> erase example4 of
        Left err -> it "Erasure of example4" $ expectationFailure (show err)
        Right counters -> do
          it "VarCounters constuction" $ do
            -- check the formation of VarCounters
            counters
              `shouldBe` makeVarCounters
                181 -- width of GF(181)
                1 -- output
                1 -- Number
                1 -- Boolean
                0 -- intermediate
                [ BoolInput 0, NumInput 0]
                [] -- custom
          it "Size of variable groups" $ do
            inputVarSize counters `shouldBe` 183
            totalBoolVarSize counters `shouldBe` 182
            boolVarsRange counters `shouldBe` (2, 184)
            numInputVarsRange counters `shouldBe` (1, 2)

          it "Index of binary representation" $ do
            lookupBinRepStart counters 0 `shouldBe` Nothing
            lookupBinRepStart counters 1 `shouldBe` Just 3
            lookupBinRepStart counters 2 `shouldBe` Nothing

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

example4 :: Comp Number
example4 = do
  boolean <- input
  number <- input
  return $ fromBool boolean + number * 2
