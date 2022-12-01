module Test.Execution where

import qualified AggregateSignature.Program as AggSig
import AggregateSignature.Util
import qualified Basic
import Keelung
import Keelung.Compiler (Error (..), execute)
import Keelung.Compiler.Interpret.Typed (InterpretError (..))
import qualified Keelung.Syntax.Typed as C
import Test.Hspec

tests :: SpecWith ()
tests = describe "Execution" $ do
  describe "Aggregate Signature" $ do
    it "dim:1 sig:1" $
      runKeelungAggSig 1 1 `shouldBe` Right []
    it "dim:1 sig:10" $
      runKeelungAggSig 1 10 `shouldBe` Right []
    it "dim:10 sig:1" $
      runKeelungAggSig 10 1 `shouldBe` Right []
    it "dim:10 sig:10" $
      runKeelungAggSig 10 10 `shouldBe` Right []
  it "identity (Num)" $
    execute Basic.identity [42] `shouldBe` Right [42 :: GF181]
  it "identity (Bool)" $
    execute Basic.identityB [1] `shouldBe` Right [1 :: GF181]
  it "identity (Bool)" $
    execute Basic.identityB [0] `shouldBe` Right [0 :: GF181]
  it "add3" $
    execute Basic.add3 [0] `shouldBe` Right [3 :: GF181]
  it "eq1 1" $
    execute Basic.eq1 [0] `shouldBe` Right [0 :: GF181]
  it "eq1 2" $
    execute Basic.eq1 [3] `shouldBe` Right [1 :: GF181]
  it "cond 1" $
    execute Basic.cond' [0] `shouldBe` Right [789 :: GF181]
  it "assert fail" $
    execute Basic.assert1 [0 :: GF181]
      `shouldBe` Left
        ( InterpretError $
            InterpretAssertionError
              (C.Boolean $ C.EqN (C.InputVarN 0) (C.ValN 3))
              [("$N0", 0)]
        )
  it "assert success" $
    execute Basic.assert1 [3] `shouldBe` Right [3 :: GF181]
  it "toArrayM" $
    execute Basic.toArrayM1 [] `shouldBe` Right ([0] :: [GF181])
  it "summation" $
    execute Basic.summation [0, 2, 4, 8 :: GF181] `shouldBe` Right [14]
  it "summation2" $
    execute Basic.summation2 [0, 2, 4, 8 :: GF181] `shouldBe` Right []
  it "assertArraysEqual" $
    execute Basic.assertArraysEqual [0, 2, 4, 8, 0, 2, 4, 8 :: GF181] `shouldBe` Right []
  it "assertArraysEqual2" $
    execute Basic.assertArraysEqual2 [0, 2, 4, 8, 0, 2, 4, 8 :: GF181] `shouldBe` Right []
  it "array1D" $
    execute (Basic.array1D 1) [2, 4 :: GF181] `shouldBe` Right []

  it "array2D 1" $
    execute (Basic.array2D 1 1) [2, 4 :: GF181] `shouldBe` Right []

  it "array2D 2" $
    execute (Basic.array2D 2 2) [0, 1, 2, 3, 0, 1, 4, 9 :: GF181] `shouldBe` Right []

  it "toArray1" $
    execute Basic.toArray1 [0 .. 7 :: GF181] `shouldBe` Right []

  it "xorLists" $
    execute Basic.xorLists [] `shouldBe` Right [1 :: GF181]

  it "dupArray" $
    execute Basic.dupArray [1] `shouldBe` Right [1 :: GF181]

  it "returnArray2" $
    execute Basic.returnArray2 [2] `shouldBe` Right [2, 4 :: GF181]

  it "arithU" $
    execute Basic.arithU0 [2, 3] `shouldBe` Right [5 :: GF181]

  it "rotateAndBitTest" $
    -- 0011 0100211003
    execute Basic.rotateAndBitTest [2, 3] `shouldBe` Right [0, 0, 1, 1 :: GF181]

runKeelungAggSig :: Int -> Int -> Either (Error GF181) [GF181]
runKeelungAggSig dimension numberOfSignatures =
  let settings =
        Settings
          { enableAggChecking = True,
            enableSizeChecking = True,
            enableLengthChecking = True
          }
      param = makeParam dimension numberOfSignatures 42 settings :: Param GF181
   in execute
        (AggSig.aggregateSignature param :: Comp ())
        (genInputFromParam param)
