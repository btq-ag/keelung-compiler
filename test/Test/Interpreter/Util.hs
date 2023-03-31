{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Interpreter.Util (runAll, runAllExceptForTheOldOptimizer, throwAll, runAndCompare, debug) where

import Control.Arrow (left)
import Control.Monad (when)
import Keelung hiding (compile, run)
import Keelung.Compiler (Error (..), toR1CS)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.ConstraintSystem qualified as Relocated
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Interpreter.Error qualified as Interpreter
import Keelung.Interpreter.R1CS qualified as R1CS
import Keelung.Interpreter.Relocated qualified as Relocated
import Keelung.Interpreter.SyntaxTree qualified as SyntaxTree
import Keelung.Syntax.Encode.Syntax qualified as Encoded
import Test.Hspec

--------------------------------------------------------------------------------

-- | syntax tree interpreter
interpretSyntaxTree :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> Either (Error n) [n]
interpretSyntaxTree prog rawPublicInputs rawPrivateInputs = do
  elab <- left LangError (elaborateAndEncode prog)
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize (Encoded.compCounters (Encoded.elabComp elab)) rawPublicInputs rawPrivateInputs)
  left (InterpretError . Interpreter.SyntaxTreeError) (SyntaxTree.run elab inputs)

-- | constraint system interpreters
r1csNew :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> Either (Error n) [n]
r1csNew prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS <$> Compiler.compileO1 prog
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case R1CS.run r1cs inputs of
    Left err -> Left (InterpretError $ Interpreter.R1CSError err)
    Right outputs -> Right (Inputs.removeBinRepsFromOutputs (r1csCounters r1cs) outputs)

r1csOld :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> Either (Error n) [n]
r1csOld prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS <$> Compiler.compileO1Old prog
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case Relocated.run r1cs inputs of
    Left err -> Left (ExecError err)
    Right outputs -> Right (Inputs.removeBinRepsFromOutputs (r1csCounters r1cs) outputs)

r1csO0New :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> Either (Error n) [n]
r1csO0New prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS . Relocated.relocateConstraintSystem <$> Compiler.compileO0 prog
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case R1CS.run r1cs inputs of
    Left err -> Left (InterpretError $ Interpreter.R1CSError err)
    Right outputs -> Right (Inputs.removeBinRepsFromOutputs (r1csCounters r1cs) outputs)

--------------------------------------------------------------------------------

-- | Expect all interpreters to return the same output
runAll' :: (GaloisField n, Integral n, Encode t, Show t) => Bool -> Comp t -> [n] -> [n] -> [n] -> IO ()
runAll' enableOldOptimizer program rawPublicInputs rawPrivateInputs expected = do
  -- syntax tree interpreter
  interpretSyntaxTree program rawPublicInputs rawPrivateInputs
    `shouldBe` Right expected
  -- constraint system interpreters
  r1csNew program rawPublicInputs rawPrivateInputs
    `shouldBe` Right expected
  r1csO0New program rawPublicInputs rawPrivateInputs
    `shouldBe` Right expected
  -- only enable testing the old optimizer when the flag is set
  when enableOldOptimizer $
    r1csOld program rawPublicInputs rawPrivateInputs
      `shouldBe` Right expected

-- | Expect all interpreters to throw an error
throwAll :: (GaloisField n, Integral n, Encode t, Show t) => Comp t -> [n] -> [n] -> Interpreter.Error n -> Error n -> IO ()
throwAll program rawPublicInputs rawPrivateInputs stError csError = do
  -- syntax tree interpreters
  interpretSyntaxTree program rawPublicInputs rawPrivateInputs
    `shouldBe` Left (InterpretError stError)
  -- constraint system interpreters
  r1csNew program rawPublicInputs rawPrivateInputs
    `shouldBe` Left csError
  r1csO0New program rawPublicInputs rawPrivateInputs
    `shouldBe` Left csError

-- | Expect all interpreters to return the same output
runAll :: (GaloisField n, Integral n, Encode t, Show t) => Comp t -> [n] -> [n] -> [n] -> IO ()
runAll = runAll' True

runAllExceptForTheOldOptimizer :: (GaloisField n, Integral n, Encode t, Show t) => Comp t -> [n] -> [n] -> [n] -> IO ()
runAllExceptForTheOldOptimizer = runAll' False

runAndCompare :: (GaloisField n, Integral n, Encode t) => Bool -> Comp t -> [n] -> [n] -> IO ()
runAndCompare enableOldOptimizer program rawPublicInputs rawPrivateInputs = do
  let expectedOutput = interpretSyntaxTree program rawPublicInputs rawPrivateInputs
  r1csNew program rawPublicInputs rawPrivateInputs
    `shouldBe` expectedOutput
  when enableOldOptimizer $
    r1csOld program rawPublicInputs rawPrivateInputs
      `shouldBe` expectedOutput
  r1csO0New program rawPublicInputs rawPrivateInputs
    `shouldBe` expectedOutput

debug :: Encode t => Comp t -> IO ()
debug program = do
  -- print $ Compiler.asGF181N $ Compiler.compileO0 program
  -- print $ Compiler.asGF181N $ Compiler.compileO1 program
  print $ Compiler.asGF181N $ Compiler.compileToModules program
  print (Compiler.asGF181N $ toR1CS <$> Compiler.compileO1 program)
