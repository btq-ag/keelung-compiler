{-# LANGUAGE DataKinds #-}

module Test.Interpreter.Misc (tests, run) where

import AggregateSignature.Program qualified as AggSig
import AggregateSignature.Util qualified as AggSig
import Hash.Poseidon qualified as Poseidon
import Keelung hiding (compile)
import Keelung.Compiler (Error (..))
import Keelung.Compiler.Compile.Error qualified as Compile
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Interpreter.Error qualified as Interpreter
import Keelung.Interpreter.SyntaxTree qualified as SyntaxTree
import Test.Hspec
import Test.Interpreter.Util

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = do
  describe "Miscellaneous" $ do
    describe "Errors" $ do
      it "missing 1 public input" $ do
        let program = complement <$> inputBool Public
        throwAll
          gf181Info
          program
          ([] :: [GF181])
          []
          (Interpreter.InputError (Inputs.PublicInputSizeMismatch 1 0))
          (InterpretError (Interpreter.InputError (Inputs.PublicInputSizeMismatch 1 0)))

      it "missing 1 private input" $ do
        let program = complement <$> inputBool Private
        throwAll
          gf181Info
          program
          ([] :: [GF181])
          []
          (Interpreter.InputError (Inputs.PrivateInputSizeMismatch 1 0))
          (InterpretError (Interpreter.InputError (Inputs.PrivateInputSizeMismatch 1 0)))

      it "assert (1 = 2) (Field)" $ do
        let program = do
              assert (1 `eq` (2 :: Field))
        throwAll
          gf181Info
          program
          ([] :: [GF181])
          []
          (Interpreter.SyntaxTreeError $ SyntaxTree.AssertionError "1 = 2")
          (CompileError (Compile.ConflictingValuesF 2 1))

      it "assert (true = false) (Boolean)" $ do
        let program = do
              assert (true `eq` false)
        throwAll
          gf181Info
          program
          ([] :: [GF181])
          []
          (Interpreter.SyntaxTreeError $ SyntaxTree.AssertionError "True = False")
          (CompileError (Compile.ConflictingValuesB True False))

      it "assert (1 = 2) (UInt)" $ do
        let program = do
              assert (1 `eq` (2 :: UInt 4))
        throwAll
          gf181Info
          program
          ([] :: [GF181])
          []
          (Interpreter.SyntaxTreeError $ SyntaxTree.AssertionError "1 = 2")
          (CompileError (Compile.ConflictingValuesU 1 2))

    describe "AggCheck" $ do
      it "dim:1 sig:1" $
        runAggCheck 1 1 []
      it "dim:1 sig:10" $
        runAggCheck 1 10 []
      it "dim:10 sig:1" $
        runAggCheck 10 1 []
      it "dim:10 sig:10" $
        runAggCheck 10 10 []

    describe "LT12289" $ do
      it "dim:1 sig:1" $
        runLT12289 1 1 []
      it "dim:1 sig:10" $
        runLT12289 1 10 []
      it "dim:10 sig:1" $
        runLT12289 10 1 []
      it "dim:10 sig:10" $
        runLT12289 10 10 []

    describe "LenCheck" $ do
      it "dim:1 sig:1" $
        runLenCheck 1 1 []
      it "dim:1 sig:10" $
        runLenCheck 1 10 []
      it "dim:10 sig:1" $
        runLenCheck 10 1 []
      it "dim:10 sig:10" $
        runLenCheck 10 10 []

    describe "Poseidon" $ do
      it "[0]" $ do
        runAll gf181Info (Poseidon.hash [0]) [] [] [969784935791658820122994814042437418105599415561111385 :: GF181]

    describe "Tests on the optimizer" $ do
      it "Multiplicative 0" $ do
        let program msg = do
              msg0 <- reuse msg
              msg1 <- reuse (msg0 + 1)
              reuse ((msg1 + 1) * (msg1 + 1))
        runAndCompare gf181Info (program 0 :: Comp Field) [0 :: N GF181] []
      it "Multiplicative 1" $ do
        let program = do
              let initState = (2, 3)
              let round' (a, b) = (a + b, a * a + b * 2)
              state1 <- reuse (round' initState) -- (5, 10)
              state2 <- reuse (round' state1) -- (15, 45)
              state3 <- reuse (round' state2) -- (60, 2025)
              return $ fst state3
        runAndCompare gf181Info (program :: Comp Field) [0 :: N GF181] []
  where
    runAggCheck :: Int -> Int -> [GF181] -> IO ()
    runAggCheck dimension numberOfSignatures outputs =
      let settings =
            AggSig.Settings
              { AggSig.enableAggChecking = True,
                AggSig.enableSizeChecking = False,
                AggSig.enableLengthChecking = False
              }
          param = AggSig.makeParam dimension numberOfSignatures 42 settings :: AggSig.Param GF181
       in runAll
            gf181Info
            (AggSig.checkAgg param :: Comp ())
            (AggSig.genInputFromParam param)
            []
            outputs

    runLT12289 :: Int -> Int -> [GF181] -> IO ()
    runLT12289 dimension numberOfSignatures outputs =
      let settings =
            AggSig.Settings
              { AggSig.enableAggChecking = False,
                AggSig.enableSizeChecking = True,
                AggSig.enableLengthChecking = False
              }
          param = AggSig.makeParam dimension numberOfSignatures 42 settings :: AggSig.Param GF181
       in runAll
            gf181Info
            (AggSig.checkSize param :: Comp ())
            (AggSig.genInputFromParam param)
            []
            outputs

    runLenCheck :: Int -> Int -> [GF181] -> IO ()
    runLenCheck dimension numberOfSignatures outputs =
      let settings =
            AggSig.Settings
              { AggSig.enableAggChecking = False,
                AggSig.enableSizeChecking = False,
                AggSig.enableLengthChecking = True
              }
          param = AggSig.makeParam dimension numberOfSignatures 42 settings :: AggSig.Param GF181
       in runAll
            gf181Info
            (AggSig.checkLength param :: Comp ())
            (AggSig.genInputFromParam param)
            []
            outputs