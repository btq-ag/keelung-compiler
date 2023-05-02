module Test.Interpreter.Util (runAll, throwAll, throwAll', runAndCompare, debug, assertSize) where

import Control.Arrow (left)
import Keelung hiding (compile, run)
import Keelung.Compiler (Error (..), toR1CS)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.ConstraintSystem qualified as Relocated
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Interpreter.Error qualified as Interpreter
import Keelung.Interpreter.R1CS qualified as R1CS
import Keelung.Interpreter.SyntaxTree qualified as SyntaxTree
import Keelung.Syntax.Encode.Syntax qualified as Encoded
import Test.Hspec
import qualified Keelung.Compiler.Relocated as Relocated

--------------------------------------------------------------------------------

-- | syntax tree interpreter
interpretSyntaxTree :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> Either (Error n) [n]
interpretSyntaxTree prog rawPublicInputs rawPrivateInputs = do
  elab <- left LangError (elaborateAndEncode prog)
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize (Encoded.compCounters (Encoded.elabComp elab)) rawPublicInputs rawPrivateInputs)
  left (InterpretError . Interpreter.SyntaxTreeError) (SyntaxTree.run elab inputs)

-- | constraint system interpreters (optimized)
interpretR1CS :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> Either (Error n) [n]
interpretR1CS prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS <$> Compiler.compileO1 prog
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case R1CS.run r1cs inputs of
    Left err -> Left (InterpretError $ Interpreter.R1CSError err)
    Right outputs -> Right (Inputs.removeBinRepsFromOutputs (r1csCounters r1cs) outputs)

-- | constraint system interpreters (unoptimized)
interpretR1CSUnoptimized :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> Either (Error n) [n]
interpretR1CSUnoptimized prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS . Relocated.relocateConstraintSystem <$> Compiler.compileO0 prog
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case R1CS.run r1cs inputs of
    Left err -> Left (InterpretError $ Interpreter.R1CSError err)
    Right outputs -> Right (Inputs.removeBinRepsFromOutputs (r1csCounters r1cs) outputs)

--------------------------------------------------------------------------------

-- | Expect all interpreters to return the same output
runAll :: (GaloisField n, Integral n, Encode t, Show t) => Comp t -> [n] -> [n] -> [n] -> IO ()
runAll program rawPublicInputs rawPrivateInputs expected = do
  -- syntax tree interpreter
  interpretSyntaxTree program rawPublicInputs rawPrivateInputs
    `shouldBe` Right expected
  -- constraint system interpreters
  interpretR1CS program rawPublicInputs rawPrivateInputs
    `shouldBe` Right expected
  interpretR1CSUnoptimized program rawPublicInputs rawPrivateInputs
    `shouldBe` Right expected

-- | Expect all interpreters to throw an error
throwAll :: (GaloisField n, Integral n, Encode t, Show t) => Comp t -> [n] -> [n] -> Interpreter.Error n -> Error n -> IO ()
throwAll program rawPublicInputs rawPrivateInputs stError csError = do
  -- syntax tree interpreters
  interpretSyntaxTree program rawPublicInputs rawPrivateInputs
    `shouldBe` Left (InterpretError stError)
  -- constraint system interpreters
  interpretR1CS program rawPublicInputs rawPrivateInputs
    `shouldBe` Left csError
  interpretR1CSUnoptimized program rawPublicInputs rawPrivateInputs
    `shouldBe` Left csError

-- | Expect all interpreters to throw an error
throwAll' :: (GaloisField n, Integral n, Encode t, Show t) => Comp t -> [n] -> [n] -> Interpreter.Error n -> Error n -> Error n -> IO ()
throwAll' program rawPublicInputs rawPrivateInputs stError csError optmError = do
  -- syntax tree interpreters
  interpretSyntaxTree program rawPublicInputs rawPrivateInputs
    `shouldBe` Left (InterpretError stError)
  -- constraint system interpreters
  interpretR1CS program rawPublicInputs rawPrivateInputs
    `shouldBe` Left optmError
  interpretR1CSUnoptimized program rawPublicInputs rawPrivateInputs
    `shouldBe` Left csError

-- | Using result of syntax tree interpreter as expected output for constraint system interpreters
runAndCompare :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> IO ()
runAndCompare program rawPublicInputs rawPrivateInputs = do
  let expectedOutput = interpretSyntaxTree program rawPublicInputs rawPrivateInputs
  interpretR1CS program rawPublicInputs rawPrivateInputs
    `shouldBe` expectedOutput
  interpretR1CSUnoptimized program rawPublicInputs rawPrivateInputs
    `shouldBe` expectedOutput

-- | Print out the result of compilation
debug :: Encode t => Comp t -> IO ()
debug program = do
  print $ Compiler.asGF181N $ Compiler.compileO0 program
  -- print $ Compiler.asGF181N $ Compiler.compileO1 program
  print $ Compiler.asGF181N $ Compiler.compileToModules program
  print (Compiler.asGF181N $ toR1CS <$> Compiler.compileO1 program)

-- | 
assertSize :: Encode t => Int -> Comp t -> IO ()
assertSize afterSize program = do
  -- case Compiler.asGF181N (Compiler.compileO0 program) of 
  --   Left err -> print err
  --   Right cs -> do
  --     Relocated.numberOfConstraints (relocateConstraintSystem cs) `shouldBe` beforeSize
  case Compiler.asGF181N (Compiler.compileO1 program) of 
    Left err -> print err
    Right cs -> do
      Relocated.numberOfConstraints cs `shouldBe` afterSize