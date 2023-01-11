{-# LANGUAGE DataKinds #-}

module Main where

import Control.Arrow (left)
import Control.Monad.Except
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as BS
import Data.Field.Galois (GaloisField)
import Data.Serialize (Serialize, decode, encode)
import Encode (serializeInputAndWitness, serializeR1CS)
import Keelung.Compiler
  ( RelocatedConstraintSystem,
    Error (..),
    compileO0Elab,
    compileO1Elab,
    compileO2Elab,
    genInputsOutputsWitnessesElab,
    interpretElab,
    toR1CS,
  )
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Compiler.Util (Witness)
import Keelung.Field
import Keelung.Syntax.Typed hiding (elaborate)
import Main.Utf8 (withUtf8)
import Option
import qualified Keelung.Compiler.Syntax.Inputs as Inputs

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
            B64 -> outputCircuit (asB64 $ compileO0Elab elaborated)
            GF181 -> outputCircuit (asGF181 $ compileO0Elab elaborated)
            BN128 -> outputCircuit (asBN128 $ compileO0Elab elaborated)
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
            B64 -> outputCircuit (asB64 $ compileO2Elab elaborated)
            GF181 -> outputCircuit (asGF181 $ compileO2Elab elaborated)
            BN128 -> outputCircuit (asBN128 $ compileO2Elab elaborated)
    Protocol Interpret -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated, [Integer])
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated, inputs) -> do
          case fieldType of
            B64 -> outputInterpretedResult (interpretElab elaborated (map fromInteger inputs) :: Either String [B64])
            GF181 -> outputInterpretedResult (interpretElab elaborated (map fromInteger inputs) :: Either String [GF181])
            BN128 -> outputInterpretedResult (interpretElab elaborated (map fromInteger inputs) :: Either String [BN128])
    Protocol GenCircuit -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> do
          case fieldType of
            B64 -> outputCircuitAndWriteFile (asB64 $ compileO1Elab elaborated)
            GF181 -> outputCircuitAndWriteFile (asGF181 $ compileO1Elab elaborated)
            BN128 -> outputCircuitAndWriteFile (asBN128 $ compileO1Elab elaborated)
    Protocol GenWitness -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated, [Integer])
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated, inputs) -> do
          case fieldType of
            B64 ->
              outputInterpretedResultAndWriteFile
                (genInputsOutputsWitnessesElab elaborated (map fromInteger inputs :: [B64]))
            GF181 ->
              outputInterpretedResultAndWriteFile
                (genInputsOutputsWitnessesElab elaborated (map fromInteger inputs :: [GF181]))
            BN128 ->
              outputInterpretedResultAndWriteFile
                (genInputsOutputsWitnessesElab elaborated (map fromInteger inputs :: [BN128]))
    Version -> putStrLn "Keelung v0.8.2"
  where
    asB64 :: Either (Error B64) (RelocatedConstraintSystem B64) -> Either (Error B64) (RelocatedConstraintSystem B64)
    asB64 = id

    asGF181 :: Either (Error GF181) (RelocatedConstraintSystem GF181) -> Either (Error GF181) (RelocatedConstraintSystem GF181)
    asGF181 = id

    asBN128 :: Either (Error BN128) (RelocatedConstraintSystem BN128) -> Either (Error BN128) (RelocatedConstraintSystem BN128)
    asBN128 = id

    outputCircuit :: (Serialize n, GaloisField n, Integral n) => Either (Error n) (RelocatedConstraintSystem n) -> IO ()
    outputCircuit cs = putStrLn $ BSC.unpack $ encode (left show (toR1CS <$> cs))

    outputCircuitAndWriteFile :: (Serialize n, GaloisField n, Integral n) => Either (Error n) (RelocatedConstraintSystem n) -> IO ()
    outputCircuitAndWriteFile cs = do
      outputCircuit cs
      case cs of
        Left _ -> return ()
        Right cs' -> do
          let r1cs = toR1CS cs'
          BS.writeFile "circuit.jsonl" (serializeR1CS r1cs)

    outputInterpretedResult :: Serialize n => Either String [n] -> IO ()
    outputInterpretedResult = putStrLn . BSC.unpack . encode

    outputInterpretedResultAndWriteFile :: (Serialize n, Integral n) => Either String (Inputs n, [n], Witness n) -> IO ()
    outputInterpretedResultAndWriteFile result = do
      -- print outputs
      outputInterpretedResult (fmap (\(_, outputs, _) -> outputs) result)

      case result of
        Left _ -> return ()
        Right (inputs, outputs, witness) -> do
          BS.writeFile "witness.jsonl" (serializeInputAndWitness (Inputs.flatten inputs) outputs witness)

run :: (GaloisField n, Integral n) => ExceptT (Error n) IO () -> IO ()
run f = do
  res <- runExceptT f
  case res of
    Left err -> print err
    Right () -> return ()
