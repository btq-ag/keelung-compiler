{-# LANGUAGE DataKinds #-}

module Main where

import qualified AggregateSignature.Program.Keelung as Keelung
import qualified AggregateSignature.Program.Snarkl as Snarkl
import AggregateSignature.Util
import qualified Basic
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Keelung
import Keelung.Constraint (cadd)
import qualified Keelung.Optimise.MinimiseConstraints as Optimise
import qualified Keelung.Optimise.Monad as Optimise
import qualified Snarkl
import Test.Hspec

-- | (1) Compile to R1CS.
--   (2) Generate a satisfying assignment, 'w'.
--   (3) Check whether 'w' satisfies the constraint system produced in (1).
--   (4) Check whether the R1CS result matches the interpreter result.
execute :: (Compilable n a, GaloisField n, Bounded n, Integral n) => Comp n a -> [n] -> Either String (Maybe n)
execute prog inputs = do
  typeErased <- erase prog
  let constraintSystem = compile typeErased
  let r1cs = toR1CS constraintSystem

  let outputVar = r1csOutputVar r1cs
  witness <- witnessOfR1CS inputs r1cs

  -- extract the output value from the witness
  actualOutput <- case outputVar of
    Nothing -> return Nothing
    Just var -> case IntMap.lookup var witness of
      Nothing ->
        Left $
          "output variable "
            ++ show outputVar
            ++ "is not mapped in\n  "
            ++ show witness
      Just value -> return $ Just value

  -- interpret the program to see if the output value is correct
  expectedOutput <- interpret prog inputs

  if actualOutput == expectedOutput && satisfyR1CS witness r1cs
    then return actualOutput
    else
      Left $
        "interpreter result "
          ++ show expectedOutput
          ++ " differs from actual result "
          ++ show actualOutput

-- return $ Result result nw ng out r1cs

runSnarklAggSig :: Int -> Int -> GF181
runSnarklAggSig dimension numberOfSignatures =
  let settings =
        Settings
          { enableAggSigChecking = True,
            enableSigSizeChecking = True,
            enableSigLengthChecking = True
          }
      setup = makeSetup dimension numberOfSignatures 42 settings :: Setup GF181
   in Snarkl.resultResult $
        Snarkl.execute
          Snarkl.Simplify
          (Snarkl.aggregateSignature setup :: Snarkl.Comp 'Snarkl.TBool GF181)
          (genInputFromSetup setup)

runKeelungAggSig :: Int -> Int -> Maybe GF181
runKeelungAggSig dimension numberOfSignatures =
  let settings =
        Settings
          { enableAggSigChecking = True,
            enableSigSizeChecking = True,
            enableSigLengthChecking = True
          }
      setup = makeSetup dimension numberOfSignatures 42 settings :: Setup GF181
      result =
        execute
          (Keelung.aggregateSignature setup :: Comp GF181 ())
          (genInputFromSetup setup)
   in case result of
        Left _ -> Nothing
        Right val -> val

main :: IO ()
main = hspec $ do
  describe "Aggregate Signature" $ do
    describe "Snarkl" $ do
      it "dim:1 sig:1" $
        runSnarklAggSig 1 1 `shouldBe` 1
      it "dim:1 sig:10" $
        runSnarklAggSig 1 10 `shouldBe` 1
      it "dim:10 sig:1" $
        runSnarklAggSig 10 1 `shouldBe` 1
      it "dim:10 sig:10" $
        runSnarklAggSig 10 10 `shouldBe` 1
    describe "Keelung" $ do
      it "dim:1 sig:1" $
        runSnarklAggSig 1 1 `shouldBe` 1
      it "dim:1 sig:10" $
        runSnarklAggSig 1 10 `shouldBe` 1
      it "dim:10 sig:1" $
        runSnarklAggSig 10 1 `shouldBe` 1
      it "dim:10 sig:10" $
        runSnarklAggSig 10 10 `shouldBe` 1

  describe "Type Erasure" $ do
    it "boolean variables in Aggregate Signature" $
      let settings =
            Settings
              { enableAggSigChecking = True,
                enableSigSizeChecking = True,
                enableSigLengthChecking = True
              }
          setup = makeSetup 1 1 42 settings :: Setup GF181
          erased = erase (Keelung.aggregateSignature setup :: Comp GF181 ())
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
  -- it "assert 1" $
  --   execute Basic.assert1 [0] `shouldBe` Right 0

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
