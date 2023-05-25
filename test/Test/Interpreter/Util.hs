module Test.Interpreter.Util (runAll, throwAll, throwAll', runAndCompare, debug, assertSize, gf181Info) where

import Control.Arrow (left)
import Data.Field.Galois
import Data.Proxy (Proxy (..), asProxyTypeOf)
import Keelung hiding (compile)
import Keelung.Compiler (Error (..), toR1CS)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.ConstraintSystem qualified as CS
import Keelung.Compiler.Linker qualified as Linker
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Interpreter.Error qualified as Interpreter
import Keelung.Interpreter.R1CS qualified as R1CS
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

-- | constraint system interpreters (optimized)
interpretR1CS :: (GaloisField n, Integral n, Encode t) => (FieldType, Integer, Integer) -> Comp t -> [n] -> [n] -> Either (Error n) [n]
interpretR1CS fieldInfo prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS <$> Compiler.compileO1 fieldInfo prog
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case R1CS.run r1cs inputs of
    Left err -> Left (InterpretError $ Interpreter.R1CSError err)
    Right outputs -> Right (Inputs.removeBinRepsFromOutputs (r1csCounters r1cs) outputs)

-- | constraint system interpreters (unoptimized)
interpretR1CSUnoptimized :: (GaloisField n, Integral n, Encode t) => (FieldType, Integer, Integer) -> Comp t -> [n] -> [n] -> Either (Error n) [n]
interpretR1CSUnoptimized fieldInfo prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS . Linker.linkConstraintModule <$> Compiler.compileO0 fieldInfo prog
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case R1CS.run r1cs inputs of
    Left err -> Left (InterpretError $ Interpreter.R1CSError err)
    Right outputs -> Right (Inputs.removeBinRepsFromOutputs (r1csCounters r1cs) outputs)

--------------------------------------------------------------------------------

-- | Expect all interpreters to return the same output
runAll :: (GaloisField n, Integral n, Encode t, Show t) => (FieldType, Integer, Integer) -> Comp t -> [n] -> [n] -> [n] -> IO ()
runAll fieldInfo program rawPublicInputs rawPrivateInputs expected = do
  -- syntax tree interpreter
  interpretSyntaxTree program rawPublicInputs rawPrivateInputs
    `shouldBe` Right expected
  -- constraint system interpreters
  interpretR1CS fieldInfo program rawPublicInputs rawPrivateInputs
    `shouldBe` Right expected
  interpretR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
    `shouldBe` Right expected

-- | Expect all interpreters to throw an error
throwAll :: (GaloisField n, Integral n, Encode t, Show t) => (FieldType, Integer, Integer) -> Comp t -> [n] -> [n] -> Interpreter.Error n -> Error n -> IO ()
throwAll fieldInfo program rawPublicInputs rawPrivateInputs stError csError = do
  -- syntax tree interpreters
  interpretSyntaxTree program rawPublicInputs rawPrivateInputs
    `shouldBe` Left (InterpretError stError)
  -- constraint system interpreters
  interpretR1CS fieldInfo program rawPublicInputs rawPrivateInputs
    `shouldBe` Left csError
  interpretR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
    `shouldBe` Left csError

-- | Expect all interpreters to throw an error
throwAll' :: (GaloisField n, Integral n, Encode t, Show t) => (FieldType, Integer, Integer) -> Comp t -> [n] -> [n] -> Interpreter.Error n -> Error n -> Error n -> IO ()
throwAll' fieldInfo program rawPublicInputs rawPrivateInputs stError csError optmError = do
  -- syntax tree interpreters
  interpretSyntaxTree program rawPublicInputs rawPrivateInputs
    `shouldBe` Left (InterpretError stError)
  -- constraint system interpreters
  interpretR1CS fieldInfo program rawPublicInputs rawPrivateInputs
    `shouldBe` Left optmError
  interpretR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
    `shouldBe` Left csError

-- | Using result of syntax tree interpreter as expected output for constraint system interpreters
runAndCompare :: (GaloisField n, Integral n, Encode t) => (FieldType, Integer, Integer) -> Comp t -> [n] -> [n] -> IO ()
runAndCompare fieldInfo program rawPublicInputs rawPrivateInputs = do
  let expectedOutput = interpretSyntaxTree program rawPublicInputs rawPrivateInputs
  interpretR1CS fieldInfo program rawPublicInputs rawPrivateInputs
    `shouldBe` expectedOutput
  interpretR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
    `shouldBe` expectedOutput

-- | Print out the result of compilation
debug :: Encode t => Comp t -> IO ()
debug program = do
  print $ Compiler.asGF181N $ Compiler.compileO0 gf181Info program
  print (Compiler.asGF181N $ toR1CS . Linker.linkConstraintModule <$> Compiler.compileO0 gf181Info program)
  -- print $ Compiler.asGF181N $ Compiler.compileO1 program
  print $ Compiler.asGF181N $ Compiler.compileToModules gf181Info program
  print (Compiler.asGF181N $ toR1CS <$> Compiler.compileO1 gf181Info program)

assertSize :: Encode t => Int -> Comp t -> IO ()
assertSize afterSize program = do
  -- case Compiler.asGF181N (Compiler.compileO0 program) of
  --   Left err -> print err
  --   Right cs -> do
  --     CS.numberOfConstraints (linkConstraintModule cs) `shouldBe` beforeSize
  case Compiler.asGF181N (Compiler.compileO1 gf181Info program) of
    Left err -> print err
    Right cs -> do
      CS.numberOfConstraints cs `shouldBe` afterSize

gf181Info :: (FieldType, Integer, Integer)
gf181Info =
  let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy GF181)
   in (gf181, toInteger (char fieldNumber), toInteger (deg fieldNumber))
