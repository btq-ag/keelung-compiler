{-# LANGUAGE DataKinds #-}

module Main where

import qualified AggregateSignature.Program as AggSig
import AggregateSignature.Util
import qualified Basic
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Keelung
import Keelung.Constraint (cadd)
import qualified Keelung.Optimise.MinimiseConstraints as Optimise
import qualified Keelung.Optimise.Monad as Optimise
import Test.Hspec

runKeelungAggSig :: Int -> Int -> Either String (Maybe GF181)
runKeelungAggSig dimension numberOfSignatures =
  let settings =
        Settings
          { enableAggChecking = False,
            enableSizeChecking = True,
            enableLengthChecking = False
          }
      param = makeParam dimension numberOfSignatures 42 settings :: Param GF181
   in execute
        (AggSig.aggregateSignature param :: Comp GF181 ())
        (genInputFromParam param)

main :: IO ()
main = hspec $ do
  describe "Aggregate Signature" $ do
    it "dim:1 sig:1" $
      runKeelungAggSig 1 1 `shouldBe` Right Nothing
  -- it "dim:1 sig:10" $
  --   runKeelungAggSig 1 10 `shouldBe` Right Nothing
  -- it "dim:10 sig:1" $
  --   runKeelungAggSig 10 1 `shouldBe` Right Nothing
  -- it "dim:10 sig:10" $
  --   runKeelungAggSig 10 10 `shouldBe` Right Nothing

  describe "Type Erasure" $ do
    it "boolean variables in Aggregate Signature" $
      let settings =
            Settings
              { enableAggChecking = True,
                enableSizeChecking = True,
                enableLengthChecking = True
              }
          setup = makeParam 1 1 42 settings :: Param GF181
          erased = erase (AggSig.aggregateSignature setup :: Comp GF181 ())
          result = IntSet.toList . erasedBooleanVars <$> erased
       in result `shouldBe` Right [3 .. 16]

  describe "Compilation" $ do
    it "identity (Num)" $
      execute Basic.identity [42] `shouldBe` Right (Just 42)
    it "identity (Bool)" $
      execute Basic.identityB [1] `shouldBe` Right (Just 1)
    it "identity (Bool)" $
      execute Basic.identityB [0] `shouldBe` Right (Just 0)
    it "add3" $
      execute Basic.add3 [0] `shouldBe` Right (Just 3)
    it "eq1 1" $
      execute Basic.eq1 [0] `shouldBe` Right (Just 0)
    it "eq1 2" $
      execute Basic.eq1 [3] `shouldBe` Right (Just 1)
    it "cond 1" $
      execute Basic.cond [0] `shouldBe` Right (Just 789)
    it "assert fail" $
      execute Basic.assert1 [0] `shouldBe` Left "Assertion failed: $0 = 3\nassignments of variables: [(0,0)]"
    it "assert success" $
      execute Basic.assert1 [3] `shouldBe` Right (Just 3)

  -- NOTE:
  --    some variables are of "don't care"
  --    they get thrown away and won't be in the witness
  -- it "cond 2" $
  --   execute Basic.cond [3] `shouldBe` Right 12

  describe "Optimisation" $ do
    -- describe "Constant Propagation" $ do
    --   it "1 + 1" $
    --     erasedExpr <$> Basic.elab Basic.constant1 `shouldBe` Right 2

    describe "Constraint Set Reduction" $ do
      it "$0 = $1" $
        let constraint = cadd 0 [(0, 1), (1, -1)]
            links = IntMap.fromList [(1, 0)]
            sizes = IntMap.fromList [(0, 2)]
            run :: Optimise.OptiM GF181 a -> a
            run = Optimise.runOptiM' links sizes mempty
         in run (Optimise.substConstraint constraint)
              `shouldBe` cadd 0 []

-- it "$0 = $1 2" $
--   let constraints = Set.singleton $ cadd 0 [(0, 1), (1, -1)]
--       run :: Optimise.OptiM GF181 a -> a
--       run = Optimise.runOptiM mempty
--       pinnedVars = [0, 1]
--   in
--     run (Optimise.simplifyConstraintSet pinnedVars constraints) `shouldBe`
--     constraints
