{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Arrow (left)
import Control.Monad.Except
import Data.ByteString.Char8 qualified as BSC
import Data.ByteString.Lazy qualified as BS
import Data.Data (Proxy (..))
import Data.Field.Galois (Binary, GaloisField (char, deg), Prime)
import Data.Proxy (asProxyTypeOf)
import Data.Serialize (Serialize, decode, encode)
import Data.Vector (Vector)
import Encode
import GHC.TypeLits
import Keelung.Compiler
  ( Error (..),
    compileO0Elab,
    compileO1Elab,
    generateWitnessElab,
    interpretElab,
    toR1CS,
  )
import Keelung.Constraint.R1CS (R1CS)
import Keelung.Field
import Keelung.Syntax.Counters
import Keelung.Syntax.Encode.Syntax
import Main.Utf8 (withUtf8)
import Option
import qualified Keelung.Compiler.Linker as Linker

type Result n = Either String (R1CS n)

type Result3 n = Either String (R1CS n)

type Result2 n = Either (Error n) (Counters, [n], Vector n)

convert :: Integral a => Result3 a -> Result3 Integer
convert (Left err) = Left err
convert (Right cs) = Right (fmap toInteger cs)

adapter ::
  (forall n. (KnownNat n) => Result (Prime n) -> IO ()) ->
  (forall n. (KnownNat n) => Result (Binary n) -> IO ()) ->
  (forall n. (KnownNat n) => (FieldType, Integer, Integer) -> Result (Prime n)) ->
  (forall n. (KnownNat n) => (FieldType, Integer, Integer) -> Result (Binary n)) ->
  FieldType ->
  IO ()
adapter funcP _ argP _ (Prime n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) ->
    let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy (Prime n))
        fieldInfo = (Prime n, toInteger (char fieldNumber), toInteger (deg fieldNumber))
     in funcP (argP fieldInfo :: Result (Prime n))
  Nothing -> return ()
adapter _ funcB _ argB (Binary n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) ->
    let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy (Binary n))
        fieldInfo = (Binary n, toInteger (char fieldNumber), toInteger (deg fieldNumber))
     in funcB (argB fieldInfo :: Result (Binary n))
  Nothing -> return ()

adapter4 ::
  (Either String (R1CS Integer) -> IO ()) ->
  (Either String (R1CS Integer) -> IO ()) ->
  (forall n. (KnownNat n) => Result (Prime n)) ->
  (forall n. (KnownNat n) => Result (Binary n)) ->
  FieldType ->
  IO ()
adapter4 funcP _ argP _ (Prime n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) -> funcP $ convert (argP :: Result (Prime n))
  Nothing -> return ()
adapter4 _ funcB _ argB (Binary n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) -> funcB $ convert (argB :: Result (Binary n))
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
  (forall n. (KnownNat n) => (FieldType, Integer, Integer) -> Result2 (Prime n)) ->
  (forall n. (KnownNat n) => (FieldType, Integer, Integer) -> Result2 (Binary n)) ->
  FieldType ->
  IO ()
adapter2 funcP _ argP _ (Prime n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) ->
    let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy (Prime n))
        fieldInfo = (Prime n, toInteger (char fieldNumber), toInteger (deg fieldNumber))
     in funcP (argP fieldInfo :: Result2 (Prime n))
  Nothing -> return ()
adapter2 _ funcB _ argB (Binary n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) ->
    let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy (Binary n))
        fieldInfo = (Binary n, toInteger (char fieldNumber), toInteger (deg fieldNumber))
     in funcB (argB fieldInfo :: Result2 (Binary n))
  Nothing -> return ()

-- formFieldInfo :: FieldType -> (FieldType, Integer, Integer)

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
          adapter
            outputCircuit
            outputCircuit
            (\fieldInfo -> left show $ toR1CS . Linker.linkConstraintModule <$> compileO0Elab fieldInfo elaborated)
            (\fieldInfo -> left show $ toR1CS . Linker.linkConstraintModule <$> compileO0Elab fieldInfo elaborated)
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
            (\fieldInfo -> left show $ toR1CS <$> compileO1Elab fieldInfo elaborated)
            (\fieldInfo -> left show $ toR1CS <$> compileO1Elab fieldInfo elaborated)
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
            (\fieldInfo -> left show $ toR1CS <$> compileO1Elab fieldInfo elaborated)
            (\fieldInfo -> left show $ toR1CS <$> compileO1Elab fieldInfo elaborated)
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
            (\fieldInfo -> left show $ toR1CS <$> compileO1Elab fieldInfo elaborated)
            (\fieldInfo -> left show $ toR1CS <$> compileO1Elab fieldInfo elaborated)
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
            (\fieldInfo -> generateWitnessElab fieldInfo elaborated (map fromInteger rawPublicInputs) (map fromInteger rawPrivateInputs))
            (\fieldInfo -> generateWitnessElab fieldInfo elaborated (map fromInteger rawPublicInputs) (map fromInteger rawPrivateInputs))
            fieldType
    Version -> putStrLn "Keelung v0.11.0"
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
