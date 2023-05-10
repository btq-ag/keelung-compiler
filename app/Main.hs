{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}


module Main where

import Control.Arrow (left)
import Control.Monad.Except
import Data.ByteString.Char8 qualified as BSC
import Data.ByteString.Lazy qualified as BS
import Data.Data (Proxy (..))
import Data.Field.Galois ( GaloisField, Binary, Prime )
import Data.Serialize (Serialize, decode, encode)
import Data.Vector (Vector)
import Encode
import GHC.TypeLits
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

type Result n = Either (Error n) (RelocatedConstraintSystem n)
type Result2 n = Either (Error n) (Counters, [n], Vector n)

adapter ::
  (forall n. (KnownNat n) => Result (Prime n) -> IO ()) ->
  (forall n. (KnownNat n) => Result (Binary n) -> IO ()) ->
  (forall n. (KnownNat n) => Result (Prime n)) ->
  (forall n. (KnownNat n) => Result (Binary n)) ->
  FieldType ->
  IO ()
adapter funcP _ argP _ (Prime n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) -> funcP (argP :: Result (Prime n))
  Nothing -> return ()
adapter _ funcB _ argB (Binary n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) -> funcB (argB :: Result (Binary n))
  Nothing -> return ()

adapter3 ::
  (forall n. (KnownNat n) => Either String [Prime n] -> IO ()) ->
  (forall n. (KnownNat n) => Either String [Binary n] -> IO ()) ->
  (forall n. (KnownNat n) => Either String [Prime n]) ->
  (forall n. (KnownNat n) => Either String [Binary n]) ->
  FieldType ->
  IO ()
adapter3 funcP _ argP _ (Prime n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) -> funcP (argP :: Either String [Prime n])
  Nothing -> return ()
adapter3 _ funcB _ argB (Binary n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) -> funcB (argB :: Either String [Binary n])
  Nothing -> return ()

adapter2 ::
  (forall n. (KnownNat n) => Result2 (Prime n) -> IO ()) ->
  (forall n. (KnownNat n) => Result2 (Binary n) -> IO ()) ->
  (forall n. (KnownNat n) => Result2 (Prime n)) ->
  (forall n. (KnownNat n) => Result2 (Binary n)) ->
  FieldType ->
  IO ()
adapter2 funcP _ argP _ (Prime n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) -> funcP (argP :: Result2 (Prime n))
  Nothing -> return ()
adapter2 _ funcB _ argB (Binary n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) -> funcB (argB :: Result2 (Binary n))
  Nothing -> return ()

main :: IO ()
main = withUtf8 $ do
  options <- getOptions
  case options of
    Protocol CompileO0 -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) ->
          adapter
            outputCircuit
            outputCircuit
            (Relocated.relocateConstraintSystem <$> compileO0OldElab elaborated)
            (Relocated.relocateConstraintSystem <$> compileO0OldElab elaborated)
            fieldType
    Protocol CompileO1 -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) ->
          adapter
            outputCircuit
            outputCircuit
            (compileO1Elab elaborated)
            (compileO1Elab elaborated)
            fieldType
    Protocol CompileO2 -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) ->
          adapter
            outputCircuit
            outputCircuit
            (compileO1OldElab elaborated)
            (compileO1OldElab elaborated)
            fieldType
    Protocol Interpret -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated, [Integer], [Integer])
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated, rawPublicInputs, rawPrivateInputs) ->
          adapter3
            outputInterpretedResult
            outputInterpretedResult
            (left show $ interpretElab elaborated (map fromInteger rawPublicInputs) (map fromInteger rawPrivateInputs))
            (left show $ interpretElab elaborated (map fromInteger rawPublicInputs) (map fromInteger rawPrivateInputs))
            fieldType
    Protocol (GenCircuit filepath) -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) ->
          adapter
            (outputCircuitAndWriteFile filepath)
            (outputCircuitAndWriteFile filepath)
            (compileO1OldElab elaborated)
            (compileO1OldElab elaborated)
            fieldType
    Protocol (GenWitness filepath) -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated, [Integer], [Integer])
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated, rawPublicInputs, rawPrivateInputs) ->

          adapter2
            (outputInterpretedResultAndWriteFile filepath)
            (outputInterpretedResultAndWriteFile filepath)
            (generateWitnessElab elaborated (map fromInteger rawPublicInputs) (map fromInteger rawPrivateInputs))
            (generateWitnessElab elaborated (map fromInteger rawPublicInputs) (map fromInteger rawPrivateInputs))
            fieldType
    Version -> putStrLn "Keelung v0.10.0"
  where

    outputCircuit :: (Serialize n, GaloisField n, Integral n) => Either (Error n) (RelocatedConstraintSystem n) -> IO ()
    outputCircuit cs = putStrLn $ BSC.unpack $ encode (left show (toR1CS <$> cs))

    outputCircuitAndWriteFile :: (Serialize n, GaloisField n, Integral n) => FilePath -> Either (Error n) (RelocatedConstraintSystem n) -> IO ()
    outputCircuitAndWriteFile filepath cs = do
      outputCircuit cs
      case cs of
        Left _ -> return ()
        Right cs' -> do
          let r1cs = toR1CS cs'
          BS.writeFile filepath (serializeR1CS r1cs)

    outputInterpretedResult :: (Serialize a, Serialize n) => Either a [n] -> IO ()
    outputInterpretedResult = putStrLn . BSC.unpack . encode

    outputInterpretedResultAndWriteFile :: (Serialize n, GaloisField n, Integral n) => FilePath -> Either (Error n) (Counters, [n], Vector n) -> IO ()
    outputInterpretedResultAndWriteFile filepath result = do
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
