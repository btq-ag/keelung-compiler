{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Test.Interpreter.Util (throwAll, debug, assertSize, gf181Info, runPrime, debugPrime, throwPrimeR1CS) where

import Control.Arrow (left, right)
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
import Keelung.Interpreter.Error qualified as Interpreter
import Keelung.Interpreter.R1CS qualified as R1CS
import Keelung.Interpreter.SyntaxTree qualified as SyntaxTree
import Keelung.Syntax.Encode.Syntax qualified as Encoded
import Test.Hspec
import Keelung.Compiler.FieldInfo

--------------------------------------------------------------------------------

-- | syntax tree interpreter
interpretSyntaxTree :: (GaloisField n, Integral n, Encode t) => Comp t -> [Integer] -> [Integer] -> Either (Error n) [Integer]
interpretSyntaxTree prog rawPublicInputs rawPrivateInputs = do
  elab <- left LangError (elaborateAndEncode prog)
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize (Encoded.compCounters (Encoded.elabComp elab)) rawPublicInputs rawPrivateInputs)
  right (map fromInteger) $ left (InterpretError . Interpreter.SyntaxTreeError) (SyntaxTree.run elab inputs)

-- | constraint system interpreters (optimized)
interpretR1CS :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> Either (Error n) [n]
interpretR1CS fieldInfo prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS <$> Compiler.compileO1 fieldInfo prog
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case R1CS.run r1cs inputs of
    Left err -> Left (InterpretError $ Interpreter.R1CSError err)
    Right outputs -> Right (toList $ Inputs.deserializeBinReps (r1csCounters r1cs) outputs)

-- | constraint system interpreters (unoptimized)
interpretR1CSUnoptimized :: (GaloisField n, Integral n, Encode t) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> Either (Error n) [n]
interpretR1CSUnoptimized fieldInfo prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS . Linker.linkConstraintModule <$> Compiler.compileO0 fieldInfo prog
  inputs <- left (InterpretError . Interpreter.InputError) (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case R1CS.run r1cs inputs of
    Left err -> Left (InterpretError $ Interpreter.R1CSError err)
    Right outputs -> Right (toList $ Inputs.deserializeBinReps (r1csCounters r1cs) outputs)

--------------------------------------------------------------------------------

-- | Expect all interpreters to throw an error
throwAll :: (GaloisField n, Integral n, Encode t, Show t) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> Interpreter.Error n -> Error n -> IO ()
throwAll fieldInfo program rawPublicInputs rawPrivateInputs stError csError = do
  -- syntax tree interpreters
  interpretSyntaxTree program rawPublicInputs rawPrivateInputs
    `shouldBe` Left (InterpretError stError)
  -- constraint system interpreters
  interpretR1CS fieldInfo program rawPublicInputs rawPrivateInputs
    `shouldBe` Left csError
  interpretR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
    `shouldBe` Left csError

-- | Print out the result of compilation
debug :: Encode t => Comp t -> IO ()
debug program = do
  -- print $ Compiler.asGF181N $ Compiler.compileO0 gf181Info program
  -- print (Compiler.asGF181N $ toR1CS . Linker.linkConstraintModule <$> Compiler.compileO0 gf181Info program)
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

gf181Info :: FieldInfo
gf181Info =
  let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy GF181)
   in FieldInfo {
        fieldTypeData = gf181,
        fieldOrder = toInteger (order fieldNumber),
        fieldChar = char fieldNumber,
        fieldDeg = fromIntegral (deg fieldNumber),
        fieldWidth = ceiling (logBase (2 :: Double) (fromIntegral (order fieldNumber)))
   }

-- prime :: Integer -> FieldInfo
-- prime n = case someNatVal (fromIntegral n) of
--   Just (SomeNat (_ :: Proxy n)) ->
--     let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy (Prime n))
--      in (Prime (fromIntegral n), ceiling (logBase (2 :: Double) (fromIntegral (order fieldNumber))), toInteger (char fieldNumber), toInteger (deg fieldNumber))
--   Nothing -> error "[ panic ] someNatVal failed"

-- deriveFieldInfo :: KnownNat n => Either (Error (Prime n)) [Prime n] -> FieldInfo
-- deriveFieldInfo result =
--   let number = natVal (deriveProxy result)
--       fieldNumber = deriveFieldNumber result
--    in (Prime (fromIntegral number), ceiling (logBase (2 :: Double) (fromIntegral (order fieldNumber))), toInteger (char fieldNumber), toInteger (deg fieldNumber))
--   where
--     deriveProxy :: KnownNat n => Either (Error (Prime n)) [Prime n] -> Proxy n
--     deriveProxy _ = Proxy

--     deriveFieldNumber :: KnownNat n => Either (Error (Prime n)) [Prime n] -> Prime n
--     deriveFieldNumber _ = asProxyTypeOf 0 Proxy

-- | Expect all interpreters to return the same output
-- runPrime :: KnownNat n => (Encode t, Show t) => Comp t -> [Integer] -> [Integer] -> [Prime n] -> IO ()
-- runPrime program rawPublicInputs rawPrivateInputs expected = do
--   -- syntax tree interpreter
--   let result = interpretSyntaxTree program rawPublicInputs rawPrivateInputs
--   let fieldInfo = deriveFieldInfo result

--   result `shouldBe` Right expected
--   -- constraint system interpreters
--   interpretR1CS fieldInfo program rawPublicInputs rawPrivateInputs
--     `shouldBe` Right expected
--   interpretR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
--     `shouldBe` Right expected

runPrime :: Encode t => FieldType -> Comp t -> [Integer] -> [Integer] -> [Integer] -> IO ()
runPrime fieldType program rawPublicInputs rawPrivateInputs expected = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime :: KnownNat n => Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      let expected' = map fromInteger expected :: [Prime n]
      interpretSyntaxTree program rawPublicInputs rawPrivateInputs `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])
      -- constraint system interpreters
      interpretR1CS fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Right expected'
      interpretR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Right expected'

    handleBinary :: KnownNat n => Proxy (Binary n) -> FieldInfo -> IO ()
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      let expected' = map fromInteger expected :: [Binary n]
      interpretSyntaxTree program rawPublicInputs rawPrivateInputs `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])
      -- constraint system interpreters
      interpretR1CS fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Right expected'
      interpretR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Right expected'

--------------------------------------------------------------------------

-- | Expect R1CS interpreters to throw an error
throwPrimeR1CS :: (GaloisField n, Integral n, Encode t, Show t) => FieldType -> Comp t -> [Integer] -> [Integer] -> Error n -> IO ()
throwPrimeR1CS fieldType program rawPublicInputs rawPrivateInputs csError = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime :: KnownNat n =>Proxy (Prime n) -> FieldInfo -> IO ()
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      -- interpretSyntaxTree program rawPublicInputs rawPrivateInputs `shouldBe` (Left (InterpretError stError) :: Either (Error (Prime n)) [Integer])
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
      -- let expected' = map fromInteger expected :: [Binary n]
      -- interpretSyntaxTree program rawPublicInputs rawPrivateInputs `shouldBe` (Right expected :: Either (Error (Prime n)) [Integer])
      -- constraint system interpreters
      -- interpretSyntaxTree program rawPublicInputs rawPrivateInputs
      --   `shouldBe` Left (InterpretError stError)
      -- constraint system interpreters
      interpretR1CS fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError
      interpretR1CSUnoptimized fieldInfo program rawPublicInputs rawPrivateInputs
        `shouldBe` Left csError


-- fromFieldType :: FieldType -> Maybe FieldInfo
-- fromFieldType (Prime n) = case someNatVal n of
--   Just (SomeNat (_ :: Proxy n)) ->
--     let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy (Prime n))
--      in Just (Prime n, ceiling (logBase (2 :: Double) (fromIntegral (order fieldNumber))), toInteger (char fieldNumber), toInteger (deg fieldNumber))
--   Nothing -> Nothing
-- fromFieldType (Binary n) = case someNatVal n of
--   Just (SomeNat (_ :: Proxy n)) ->
--     let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy (Binary n))
--      in Just (Binary n, ceiling (logBase (2 :: Double) (fromIntegral (order fieldNumber))), toInteger (char fieldNumber), toInteger (deg fieldNumber))
--   Nothing -> Nothing

-- caseFieldType ::
--   FieldType ->
--   (forall n. KnownNat n => FieldInfo -> Proxy (Prime n) -> IO ()) ->
--   (forall n. KnownNat n => FieldInfo -> Proxy (Binary n) -> IO ()) ->
--   IO ()
-- caseFieldType (Prime n) funcPrime _ = case someNatVal n of
--   Just (SomeNat (_ :: Proxy n)) -> do
--     let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy (Prime n))
--      in funcPrime (Prime n, ceiling (logBase (2 :: Double) (fromIntegral (order fieldNumber))), toInteger (char fieldNumber), toInteger (deg fieldNumber)) (Proxy :: Proxy (Prime n))
--   Nothing -> return ()
-- caseFieldType (Binary n) _ funcBinary = case someNatVal n of
--   Just (SomeNat (_ :: Proxy n)) ->
--     let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy (Binary n))
--      in funcBinary (Binary n, ceiling (logBase (2 :: Double) (fromIntegral (order fieldNumber))), toInteger (char fieldNumber), toInteger (deg fieldNumber)) (Proxy :: Proxy (Binary n))
--   Nothing -> return ()

debugPrime :: Encode t => FieldType -> Comp t -> IO ()
debugPrime fieldType program = caseFieldType fieldType handlePrime handleBinary
  where 
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
          print (Compiler.compileToModules fieldInfo program :: Either (Error (N (Prime n))) (ConstraintModule (N (Prime n))))
          print (toR1CS <$> Compiler.compileO1 fieldInfo program :: Either (Error (N (Prime n))) (R1CS (N (Prime n))))
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
          print (Compiler.compileToModules fieldInfo program :: Either (Error (N (Binary n))) (ConstraintModule (N (Binary n))))
          print (toR1CS <$> Compiler.compileO1 fieldInfo program :: Either (Error (N (Binary n))) (R1CS (N (Binary n))))
  