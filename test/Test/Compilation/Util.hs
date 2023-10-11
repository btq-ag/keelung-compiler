{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Util (debug, debugUnoptimized, assertSize, gf181Info, runAll, throwR1CS, throwBoth, printLog, printLogUnoptimized) where

import Control.Arrow (left)
import Data.Field.Galois
import Data.Foldable (toList)
import Data.Proxy (Proxy (..), asProxyTypeOf)
import GHC.TypeLits
import Keelung hiding (Elaborated, compile)
import Keelung.Compiler (Error (..), toR1CS)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.ConstraintModule (ConstraintModule)
import Keelung.Compiler.ConstraintSystem qualified as CS
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Data.FieldInfo
import Keelung.Interpreter qualified as Interpreter
import Keelung.Solver qualified as Solver
import Keelung.Syntax.Encode.Syntax qualified as Encoded
import Test.Hspec

--------------------------------------------------------------------------------

-- | syntax tree interpreter
interpretSyntaxTree :: (GaloisField n, Integral n, Encode t) => Comp t -> [Integer] -> [Integer] -> Either (Error n) [Integer]
interpretSyntaxTree prog rawPublicInputs rawPrivateInputs = do
  elab <- left LangError (elaborateAndEncode prog)
  inputs <- left InputError (Inputs.deserialize (Encoded.compCounters (Encoded.elabComp elab)) rawPublicInputs rawPrivateInputs)
  left InterpreterError (Interpreter.run elab inputs)

-- | R1CS witness solver (on optimized R1CS)
solverR1CS :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> Either (Error n) [Integer]
solverR1CS fieldInfo prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS <$> Compiler.compileAndLinkO1 fieldInfo prog
  inputs <- left InputError (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case Solver.run r1cs inputs of
    Left err -> Left (SolverError err)
    Right (outputs, _) -> Right (toList $ Inputs.deserializeBinReps (r1csCounters r1cs) outputs)

-- | Generate R1CS witness solver report (on optimized R1CS)
solverR1CSCollectLog :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> (Maybe (Error n), Maybe (Solver.LogReport n))
solverR1CSCollectLog fieldInfo prog rawPublicInputs rawPrivateInputs = case do
  r1cs <- toR1CS <$> Compiler.compileAndLinkO1 fieldInfo prog
  inputs <- left InputError (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  return (r1cs, inputs) of
  Left err -> (Just err, Nothing)
  Right (r1cs, inputs) -> case Solver.debug r1cs inputs of
    (Left err, logs) -> (Just (SolverError err), logs)
    (Right _, logs) -> (Nothing, logs)

-- | R1CS witness solver (on unoptimized R1CS)
solverR1CSUnoptimized :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> Either (Error n) [Integer]
solverR1CSUnoptimized fieldInfo prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS <$> Compiler.compileAndLinkO0 fieldInfo prog
  inputs <- left InputError (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case Solver.run r1cs inputs of
    Left err -> Left (SolverError err)
    Right (outputs, _) -> Right (toList $ Inputs.deserializeBinReps (r1csCounters r1cs) outputs)

-- | Generate R1CS witness solver report (on unoptimized R1CS)
solverR1CSCollectLogUnoptimized :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> (Maybe (Error n), Maybe (Solver.LogReport n))
solverR1CSCollectLogUnoptimized fieldInfo prog rawPublicInputs rawPrivateInputs = case do
  r1cs <- toR1CS <$> Compiler.compileAndLinkO0 fieldInfo prog
  inputs <- left InputError (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  return (r1cs, inputs) of
  Left err -> (Just err, Nothing)
  Right (r1cs, inputs) -> case Solver.debug r1cs inputs of
    (Left err, logs) -> (Just (SolverError err), logs)
    (Right _, logs) -> (Nothing, logs)

--------------------------------------------------------------------------------

-- | Print out the result of compilation
debug :: Encode t => FieldType -> Comp t -> IO ()
debug fieldType program = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      print (Compiler.compileO1 fieldInfo program :: Either (Error (N (Prime n))) (ConstraintModule (N (Prime n))))
      print (toR1CS <$> Compiler.compileAndLinkO1 fieldInfo program :: Either (Error (N (Prime n))) (R1CS (N (Prime n))))
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      print (Compiler.compileO1 fieldInfo program :: Either (Error (N (Binary n))) (ConstraintModule (N (Binary n))))
      print (toR1CS <$> Compiler.compileAndLinkO1 fieldInfo program :: Either (Error (N (Binary n))) (R1CS (N (Binary n))))

debugUnoptimized :: Encode t => FieldType -> Comp t -> IO ()
debugUnoptimized fieldType program = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      print (Compiler.compileO0 fieldInfo program :: Either (Error (N (Prime n))) (ConstraintModule (N (Prime n))))
      print (toR1CS <$> Compiler.compileAndLinkO0 fieldInfo program :: Either (Error (N (Prime n))) (R1CS (N (Prime n))))
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      print (Compiler.compileO0 fieldInfo program :: Either (Error (N (Binary n))) (ConstraintModule (N (Binary n))))
      print (toR1CS <$> Compiler.compileAndLinkO0 fieldInfo program :: Either (Error (N (Binary n))) (R1CS (N (Binary n))))

assertSize :: Encode t => Int -> Comp t -> IO ()
assertSize afterSize program = do
  case Compiler.asGF181N (Compiler.compileAndLinkO1 gf181Info program) of
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
      solverR1CS fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])
      -- solverR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
      --   `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])

    handleBinary :: KnownNat n => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      interpretSyntaxTree program rawPublicInputs rawPrivateInputs `shouldBe` (Right expected :: Either (Error (Binary n)) [Integer])
      -- constraint system interpreters
      solverR1CS fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])
      solverR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])

printLog :: Encode t => FieldType -> Comp t -> [Integer] -> [Integer] -> IO ()
printLog fieldType program rawPublicInputs rawPrivateInputs = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime :: KnownNat n => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      let (err, logs) = solverR1CSCollectLog fieldInfo program rawPublicInputs rawPrivateInputs :: (Maybe (Error (Prime n)), Maybe (Solver.LogReport (Prime n)))
      mapM_ print err
      mapM_ print logs

    handleBinary :: KnownNat n => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      let (err, logs) = solverR1CSCollectLog fieldInfo program rawPublicInputs rawPrivateInputs :: (Maybe (Error (Binary n)), Maybe (Solver.LogReport (Binary n)))
      mapM_ print err
      mapM_ print logs

printLogUnoptimized :: Encode t => FieldType -> Comp t -> [Integer] -> [Integer] -> IO ()
printLogUnoptimized fieldType program rawPublicInputs rawPrivateInputs = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime :: KnownNat n => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      let (err, logs) = solverR1CSCollectLogUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs :: (Maybe (Error (Prime n)), Maybe (Solver.LogReport (Prime n)))
      mapM_ print err
      mapM_ print logs

    handleBinary :: KnownNat n => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      let (err, logs) = solverR1CSCollectLogUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs :: (Maybe (Error (Binary n)), Maybe (Solver.LogReport (Binary n)))
      mapM_ print err
      mapM_ print logs

--       do
-- -- constraint system interpreters
-- let result = solverR1CSDebug (Prime prime) program rawPublicInputs rawPrivateInputs
-- case result of
--   Left err -> print err
--   Right outputs -> outputs `shouldBe` expected
-- return logs

--------------------------------------------------------------------------

-- | Expect R1CS interpreters to throw an error
throwR1CS :: (GaloisField n, Integral n, Encode t, Show t) => FieldType -> Comp t -> [Integer] -> [Integer] -> Error n -> IO ()
throwR1CS fieldType program rawPublicInputs rawPrivateInputs csError = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime :: KnownNat n => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      -- syntax tree interpreters
      -- interpretSyntaxTree program rawPublicInputs rawPrivateInputs
      --   `shouldBe` Left (InterpreterError stError)
      -- constraint system interpreters
      solverR1CS fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError
      solverR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError

    handleBinary :: KnownNat n => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      -- constraint system interpreters
      -- interpretSyntaxTree program rawPublicInputs rawPrivateInputs
      --   `shouldBe` Left (InterpreterError stError)
      -- constraint system interpreters
      solverR1CS fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError
      solverR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError

throwBoth :: (GaloisField n, Integral n, Encode t, Show t) => FieldType -> Comp t -> [Integer] -> [Integer] -> Error n -> Error n -> IO ()
throwBoth fieldType program rawPublicInputs rawPrivateInputs stError csError = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime :: KnownNat n => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      -- syntax tree interpreters
      interpretSyntaxTree program rawPublicInputs rawPrivateInputs
        `shouldBe` Left stError
      -- constraint system interpreters
      solverR1CS fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError
      solverR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError

    handleBinary :: KnownNat n => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      -- constraint system interpreters
      interpretSyntaxTree program rawPublicInputs rawPrivateInputs
        `shouldBe` Left stError
      -- constraint system interpreters
      solverR1CS fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError
      solverR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError