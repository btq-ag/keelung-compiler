{-# LANGUAGE DataKinds #-}

module Test.Compilation.Misc (tests, run) where

import Hash.Poseidon qualified as Poseidon
import Keelung hiding (compile)
import Keelung.Compiler (Error (..))
import Keelung.Compiler.Compile.Error qualified as Compile
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Test.Hspec
import Test.Compilation.Util
import qualified Keelung.Interpreter as Interpreter

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = do
  describe "Miscellaneous" $ do
    describe "Errors" $ do
      it "missing 1 public input" $ do
        let program = complement <$> inputBool Public
        throwErrors
          gf181
          program
          []
          []
          (InputError (Inputs.PublicInputSizeMismatch 1 0))
          (InputError (Inputs.PublicInputSizeMismatch 1 0) :: Error GF181)

      it "missing 1 private input" $ do
        let program = complement <$> inputBool Private
        throwErrors
          gf181
          program
          []
          []
          (InputError (Inputs.PrivateInputSizeMismatch 1 0))
          (InputError (Inputs.PrivateInputSizeMismatch 1 0) :: Error GF181)

      it "assert (1 = 2) (Field)" $ do
        let program = do
              assert (1 `eq` (2 :: Field))
        throwErrors
          gf181
          program
          []
          []
          (InterpreterError (Interpreter.AssertionError "1 = 2"))
          (CompilerError (Compile.ConflictingValuesF 1 2) :: Error GF181)

      it "assert (true = false) (Boolean)" $ do
        let program = do
              assert (true `eq` false)
        throwErrors
          gf181
          program
          []
          []
          (InterpreterError (Interpreter.AssertionError "True = False"))
          (CompilerError (Compile.ConflictingValuesB True False) :: Error GF181)

      it "assert (1 = 2) (UInt)" $ do
        let program = do
              assert (1 `eq` (2 :: UInt 4))
        throwErrors
          gf181
          program
          []
          []
          (InterpreterError (Interpreter.AssertionError "1 = 2"))
          (CompilerError (Compile.ConflictingValuesU 1 2) :: Error GF181)

    describe "Poseidon" $ do
      it "[0]" $ do
        testCompiler gf181 (Poseidon.hash [0]) [] [] [969784935791658820122994814042437418105599415561111385]

      it "[0, 0]" $ do
        testCompiler gf181 (Poseidon.hash [0, 0]) [] [] [1463644445890192529906304324019268768608065984595443732]

      it "[0, 0, 0]" $ do
        testCompiler gf181 (Poseidon.hash [0, 0, 0]) [] [] [30188980558117151136401211469358799167139495293483122]