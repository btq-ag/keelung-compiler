{-# LANGUAGE DataKinds #-}

module Main where

import Control.Arrow (left)
import Control.Monad.Except
import Data.ByteString.Char8 qualified as BSC
import Data.ByteString.Lazy qualified as BS
import Data.Field.Galois (GaloisField)
import Data.Serialize (Serialize, decode, encode)
import Data.Vector (Vector)
import Encode
import Keelung.Compiler
  ( Error (..),
    RelocatedConstraintSystem,
    compileO0OldElab,
    compileO1Elab,
    compileO1OldElab,
    generateWitnessElab,
    interpretElab,
    toR1CS,
  )
import Keelung.Compiler.ConstraintSystem qualified as Relocated
import Keelung.Field
import Keelung.Syntax.Counters
import Keelung.Syntax.Encode.Syntax
import Main.Utf8 (withUtf8)
import Option

main :: IO ()
main = withUtf8 $ do
  options <- getOptions
  case options of
    Protocol CompileO0 -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> do
          case fieldType of
            B64 -> outputCircuit (asB64 $ Relocated.relocateConstraintSystem <$> compileO0OldElab elaborated)
            GF181 -> outputCircuit (asGF181 $ Relocated.relocateConstraintSystem <$> compileO0OldElab elaborated)
            BN128 -> outputCircuit (asBN128 $ Relocated.relocateConstraintSystem <$> compileO0OldElab elaborated)
    Protocol CompileO1 -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> do
          case fieldType of
            B64 -> outputCircuit (asB64 $ compileO1Elab elaborated)
            GF181 -> outputCircuit (asGF181 $ compileO1Elab elaborated)
            BN128 -> outputCircuit (asBN128 $ compileO1Elab elaborated)
    Protocol CompileO2 -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> do
          case fieldType of
            B64 -> outputCircuit (asB64 $ compileO1OldElab elaborated)
            GF181 -> outputCircuit (asGF181 $ compileO1OldElab elaborated)
            BN128 -> outputCircuit (asBN128 $ compileO1OldElab elaborated)
    Protocol Interpret -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated, [Integer], [Integer])
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated, rawPublicInputs, rawPrivateInputs) -> do
          case fieldType of
            B64 -> outputInterpretedResult (left show $ interpretElab elaborated (map fromInteger rawPublicInputs) (map fromInteger rawPrivateInputs) :: Either String [B64])
            GF181 -> outputInterpretedResult (left show $ interpretElab elaborated (map fromInteger rawPublicInputs) (map fromInteger rawPrivateInputs) :: Either String [GF181])
            BN128 -> outputInterpretedResult (left show $ interpretElab elaborated (map fromInteger rawPublicInputs) (map fromInteger rawPrivateInputs) :: Either String [BN128])
    Protocol (GenCircuit filepath) -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> do
          case fieldType of
            B64 -> outputCircuitAndWriteFile (asB64 $ compileO1OldElab elaborated) filepath
            GF181 -> outputCircuitAndWriteFile (asGF181 $ compileO1OldElab elaborated) filepath
            BN128 -> outputCircuitAndWriteFile (asBN128 $ compileO1OldElab elaborated) filepath
    Protocol (GenWitness filepath) -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated, [Integer], [Integer])
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated, rawPublicInputs, rawPrivateInputs) -> do
          case fieldType of
            B64 ->
              outputInterpretedResultAndWriteFile
                (generateWitnessElab elaborated (map fromInteger rawPublicInputs :: [B64]) (map fromInteger rawPrivateInputs :: [B64]))
                filepath
            GF181 ->
              outputInterpretedResultAndWriteFile
                (generateWitnessElab elaborated (map fromInteger rawPublicInputs :: [GF181]) (map fromInteger rawPrivateInputs :: [GF181]))
                filepath
            BN128 ->
              outputInterpretedResultAndWriteFile
                (generateWitnessElab elaborated (map fromInteger rawPublicInputs :: [BN128]) (map fromInteger rawPrivateInputs :: [BN128]))
                filepath
    Version -> putStrLn "Keelung v0.9.4"
  where
    asB64 :: Either (Error B64) (RelocatedConstraintSystem B64) -> Either (Error B64) (RelocatedConstraintSystem B64)
    asB64 = id

    asGF181 :: Either (Error GF181) (RelocatedConstraintSystem GF181) -> Either (Error GF181) (RelocatedConstraintSystem GF181)
    asGF181 = id

    asBN128 :: Either (Error BN128) (RelocatedConstraintSystem BN128) -> Either (Error BN128) (RelocatedConstraintSystem BN128)
    asBN128 = id

    outputCircuit :: (Serialize n, GaloisField n, Integral n) => Either (Error n) (RelocatedConstraintSystem n) -> IO ()
    outputCircuit cs = putStrLn $ BSC.unpack $ encode (left show (toR1CS <$> cs))

    outputCircuitAndWriteFile :: (Serialize n, GaloisField n, Integral n) => Either (Error n) (RelocatedConstraintSystem n) -> FilePath -> IO ()
    outputCircuitAndWriteFile cs filepath = do
      outputCircuit cs
      case cs of
        Left _ -> return ()
        Right cs' -> do
          let r1cs = toR1CS cs'
          BS.writeFile filepath (serializeR1CS r1cs)

    outputInterpretedResult :: (Serialize a, Serialize n) => Either a [n] -> IO ()
    outputInterpretedResult = putStrLn . BSC.unpack . encode

    outputInterpretedResultAndWriteFile :: (Serialize n, GaloisField n, Integral n) => Either (Error n) (Counters, [n], Vector n) -> FilePath -> IO ()
    outputInterpretedResultAndWriteFile result filepath = do
      -- print outputs
      outputInterpretedResult (fmap (\(_, outputs, _) -> outputs) result)
      case result of
        Left _ -> return ()
        Right (counters, _, witness) -> do
          BS.writeFile filepath (serializeInputAndWitness counters witness)

run :: (GaloisField n, Integral n) => ExceptT (Error n) IO () -> IO ()
run f = do
  res <- runExceptT f
  case res of
    Left err -> print err
    Right () -> return ()
