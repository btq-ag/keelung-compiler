module Test.Execution where

import qualified AggregateSignature.Program as AggSig
import AggregateSignature.Util
import qualified Basic
import Keelung
import Keelung.Compiler (Error (..), execute)
-- import Keelung.Interpreter.Typed (InterpretError (..))
-- import qualified Keelung.Syntax.Typed as Typed
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
  -- it "assert fail" $
  --   execute Basic.assert1 [0 :: GF181]
  --     `shouldBe` Left
  --       ( InterpretError $
  --           InterpretAssertionError
  --             (Typed.Boolean $ Typed.EqF (Typed.VarFI 0) (Typed.ValF 3))
  --             [("$FI0", 0)]
  --       )
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
