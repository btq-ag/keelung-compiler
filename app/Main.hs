{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Arrow (left)
import Control.Monad.Except
import Data.ByteString.Char8 qualified as BSC
import Data.ByteString.Lazy qualified as BS
import Data.Data (Proxy (..))
-- import Data.Field.Galois (Binary, GaloisField (order), Prime)
import Data.Foldable (toList)
import Data.Serialize (Serialize, decode, encode)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Encode
import Keelung.Compiler
  ( Error (..),
    compileO0Elab,
    compileO1Elab,
    generateWitnessElab,
    interpretElab,
    toR1CS,
  )
import Keelung.Compiler.Linker qualified as Linker
import Keelung.Constraint.R1CS (R1CS)
import Keelung.Field
import Keelung.Syntax.Counters
import Keelung.Syntax.Encode.Syntax
import Main.Utf8 (withUtf8)
import Option
import Keelung.Data.FieldInfo
import Data.Field.Galois (GaloisField, Prime, Binary)

convert :: Integral n => Either String (R1CS n) -> Either String (R1CS Integer)
convert (Left err) = Left err
convert (Right cs) = Right (fmap toInteger cs)

main :: IO ()
main = withUtf8 $ do
  options <- getOptions
  case options of
    Protocol CompileO0 -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> caseFieldType fieldType handlePrime handleBinary
          where 
            handlePrime (Proxy :: Proxy (Prime n)) fieldInfo = outputCircuit (left show $ toR1CS . Linker.linkConstraintModule <$> compileO0Elab fieldInfo elaborated :: Either String (R1CS (Prime n)))
            handleBinary (Proxy :: Proxy (Binary n)) fieldInfo = outputCircuit (left show $ toR1CS . Linker.linkConstraintModule <$> compileO0Elab fieldInfo elaborated :: Either String (R1CS (Binary n)))
    Protocol CompileO1 -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> caseFieldType fieldType handlePrime handleBinary
          where 
            handlePrime (Proxy :: Proxy (Prime n)) fieldInfo = outputCircuit (left show $ toR1CS <$> compileO1Elab fieldInfo elaborated :: Either String (R1CS (Prime n)))
            handleBinary (Proxy :: Proxy (Binary n)) fieldInfo = outputCircuit (left show $ toR1CS <$> compileO1Elab fieldInfo elaborated :: Either String (R1CS (Binary n)))
    Protocol CompileO2 -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> caseFieldType fieldType handlePrime handleBinary
          where 
            handlePrime (Proxy :: Proxy (Prime n)) fieldInfo = outputCircuit (left show $ toR1CS <$> compileO1Elab fieldInfo elaborated :: Either String (R1CS (Prime n)))
            handleBinary (Proxy :: Proxy (Binary n)) fieldInfo = outputCircuit (left show $ toR1CS <$> compileO1Elab fieldInfo elaborated :: Either String (R1CS (Binary n)))
    Protocol Interpret -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated, [Integer], [Integer])
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated, rawPublicInputs, rawPrivateInputs) -> caseFieldType fieldType handlePrime handleBinary
          where 
            handlePrime (Proxy :: Proxy (Prime n)) _fieldInfo = outputInterpretedResult (Vector.fromList <$> left show (interpretElab elaborated rawPublicInputs rawPrivateInputs :: Either (Error (Prime n)) [Integer]))
            handleBinary (Proxy :: Proxy (Binary n)) _fieldInfo = outputInterpretedResult (Vector.fromList <$> left show (interpretElab elaborated rawPublicInputs rawPrivateInputs :: Either (Error (Binary n)) [Integer]))
    Protocol (GenCircuit filepath) -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> caseFieldType fieldType handlePrime handleBinary
          where 
            handlePrime (Proxy :: Proxy (Prime n)) fieldInfo = outputCircuitAndWriteFile filepath (left show $ toR1CS <$> compileO1Elab fieldInfo elaborated :: Either String (R1CS (Prime n)))
            handleBinary (Proxy :: Proxy (Binary n)) fieldInfo = outputCircuitAndWriteFile filepath (left show $ toR1CS <$> compileO1Elab fieldInfo elaborated :: Either String (R1CS (Binary n)))
    Protocol (GenWitness filepath) -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated, [Integer], [Integer])
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated, rawPublicInputs, rawPrivateInputs) -> caseFieldType fieldType handlePrime handleBinary
          where 
            handlePrime (Proxy :: Proxy (Prime n)) fieldInfo = outputInterpretedResultAndWriteFile filepath (generateWitnessElab fieldInfo elaborated (map fromInteger rawPublicInputs) (map fromInteger rawPrivateInputs) :: Either (Error (Prime n)) (Counters, Vector (Prime n), Vector (Prime n)))
            handleBinary (Proxy :: Proxy (Binary n)) fieldInfo = outputInterpretedResultAndWriteFile filepath (generateWitnessElab fieldInfo elaborated (map fromInteger rawPublicInputs) (map fromInteger rawPrivateInputs) :: Either (Error (Binary n)) (Counters, Vector (Binary n), Vector (Binary n)))
    Version -> putStrLn $ "Keelung v" ++ versionString
  where
    outputCircuit :: Serialize a => a -> IO ()
    outputCircuit = putStrLn . BSC.unpack . encode

    outputCircuitAndWriteFile :: (Serialize n, GaloisField n, Integral n) => FilePath -> Either String (R1CS n) -> IO ()
    outputCircuitAndWriteFile filepath r1cs = do
      outputCircuit r1cs
      case r1cs of
        Left _ -> return ()
        Right r1cs' -> do
          BS.writeFile filepath (serializeR1CS r1cs')

    outputInterpretedResult :: (Serialize a, Serialize n) => Either a (Vector n) -> IO ()
    outputInterpretedResult = putStrLn . BSC.unpack . encode . fmap toList

    outputInterpretedResultAndWriteFile :: (Serialize n, GaloisField n, Integral n) => FilePath -> Either (Error n) (Counters, Vector n, Vector n) -> IO ()
    outputInterpretedResultAndWriteFile filepath result = do
      case result of
        Left err -> putStrLn $ BSC.unpack $ encode err
        Right (counters, _, witness) -> do
            outputInterpretedResult (fmap (\(_, outputs, _) -> outputs) result)
            BS.writeFile filepath (serializeInputAndWitness counters witness)

run :: (GaloisField n, Integral n) => ExceptT (Error n) IO () -> IO ()
run f = do
  res <- runExceptT f
  case res of
    Left err -> print err
    Right () -> return ()
