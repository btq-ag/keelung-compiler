{-# LANGUAGE DataKinds #-}

module Test.Interpreter.Misc (tests, run) where

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
          (CompileError (Compile.ConflictingValuesF 1 2))

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