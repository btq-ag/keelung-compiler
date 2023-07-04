{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Interpreter.Util (debug, assertSize, gf181Info, runAll, throwR1CS, throwBoth) where

import Control.Arrow (left)
import Data.Field.Galois
import Data.Foldable (toList)
import Data.Proxy (Proxy (..), asProxyTypeOf)
import GHC.TypeLits
import Keelung hiding (compile)
import Keelung.Compiler (Error (..), toR1CS)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.ConstraintModule (ConstraintModule)
import Keelung.Compiler.ConstraintSystem qualified as CS
import Keelung.Compiler.Linker qualified as Linker
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Data.FieldInfo
import Keelung.Interpreter.Error qualified as Interpreter
import Keelung.Interpreter.R1CS qualified as R1CS
import Keelung.Interpreter.SyntaxTree qualified as SyntaxTree
import Keelung.Syntax.Encode.Syntax qualified as Encoded
import Test.Hspec

--------------------------------------------------------------------------------

-- | syntax tree interpreter
interpretSyntaxTree :: (GaloisField n, Integral n, Encode t) => Comp t -> [Integer] -> [Integer] -> Either (Error n) [Integer]
interpretSyntaxTree prog rawPublicInputs rawPrivateInputs = do
  elab <- left LangError (elaborateAndEncode prog)
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize (Encoded.compCounters (Encoded.elabComp elab)) rawPublicInputs rawPrivateInputs)
  left (InterpretError . Interpreter.SyntaxTreeError) (SyntaxTree.run elab inputs)

-- | constraint system interpreters (optimized)
interpretR1CS :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> Either (Error n) [Integer]
interpretR1CS fieldInfo prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS <$> Compiler.compileO1 fieldInfo prog
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case R1CS.run r1cs inputs of
    Left err -> Left (InterpretError $ Interpreter.R1CSError err)
    Right outputs -> Right (toList $ Inputs.deserializeBinReps (r1csCounters r1cs) outputs)

-- | constraint system interpreters (unoptimized)
interpretR1CSUnoptimized :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> Either (Error n) [Integer]
interpretR1CSUnoptimized fieldInfo prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS . Linker.linkConstraintModule <$> Compiler.compileO0 fieldInfo prog
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case R1CS.run r1cs inputs of
    Left err -> Left (InterpretError $ Interpreter.R1CSError err)
    Right outputs -> Right (toList $ Inputs.deserializeBinReps (r1csCounters r1cs) outputs)

--------------------------------------------------------------------------------

-- | Print out the result of compilation
debug :: Encode t => FieldType -> Comp t -> IO ()
debug fieldType program = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      print (Compiler.compileToModules fieldInfo program :: Either (Error (N (Prime n))) (ConstraintModule (N (Prime n))))
      print (toR1CS <$> Compiler.compileO1 fieldInfo program :: Either (Error (N (Prime n))) (R1CS (N (Prime n))))
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      print (Compiler.compileToModules fieldInfo program :: Either (Error (N (Binary n))) (ConstraintModule (N (Binary n))))
      print (toR1CS <$> Compiler.compileO1 fieldInfo program :: Either (Error (N (Binary n))) (R1CS (N (Binary n))))

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

gf181Info :: FieldInfo
gf181Info =
  let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy GF181)
   in FieldInfo
        { fieldTypeData = gf181,
          fieldOrder = toInteger (order fieldNumber),
          fieldChar = char fieldNumber,
          fieldDeg = fromIntegral (deg fieldNumber),
          fieldWidth = floor (logBase (2 :: Double) (fromIntegral (order fieldNumber)))
        }

runAll :: Encode t => FieldType -> Comp t -> [Integer] -> [Integer] -> [Integer] -> IO ()
runAll fieldType program rawPublicInputs rawPrivateInputs expected = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime :: KnownNat n => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      interpretSyntaxTree program rawPublicInputs rawPrivateInputs `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])
      -- constraint system interpreters
      interpretR1CS fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])
      interpretR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])

    handleBinary :: KnownNat n => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      interpretSyntaxTree program rawPublicInputs rawPrivateInputs `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])
      -- constraint system interpreters
      interpretR1CS fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])
      interpretR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])

--------------------------------------------------------------------------

-- | Expect R1CS interpreters to throw an error
throwR1CS :: (GaloisField n, Integral n, Encode t, Show t) => FieldType -> Comp t -> [Integer] -> [Integer] -> Error n -> IO ()
throwR1CS fieldType program rawPublicInputs rawPrivateInputs csError = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime :: KnownNat n => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      -- syntax tree interpreters
      -- interpretSyntaxTree program rawPublicInputs rawPrivateInputs
      --   `shouldBe` Left (InterpretError stError)
      -- constraint system interpreters
      interpretR1CS fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError
      interpretR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError

    handleBinary :: KnownNat n => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      -- constraint system interpreters
      -- interpretSyntaxTree program rawPublicInputs rawPrivateInputs
      --   `shouldBe` Left (InterpretError stError)
      -- constraint system interpreters
      interpretR1CS fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError
      interpretR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError

throwBoth :: (GaloisField n, Integral n, Encode t, Show t) => FieldType -> Comp t -> [Integer] -> [Integer] -> Interpreter.Error n -> Error n -> IO ()
throwBoth fieldType program rawPublicInputs rawPrivateInputs stError csError = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime :: KnownNat n => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      -- syntax tree interpreters
      interpretSyntaxTree program rawPublicInputs rawPrivateInputs
        `shouldBe` Left (InterpretError stError)
      -- constraint system interpreters
      interpretR1CS fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError
      interpretR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError

    handleBinary :: KnownNat n => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      -- constraint system interpreters
      interpretSyntaxTree program rawPublicInputs rawPrivateInputs
        `shouldBe` Left (InterpretError stError)
      -- constraint system interpreters
      interpretR1CS fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError
      interpretR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError