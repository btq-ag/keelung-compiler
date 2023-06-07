{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Arrow (left)
import Control.Monad.Except
import Data.ByteString.Char8 qualified as BSC
import Data.ByteString.Lazy qualified as BS
import Data.Data (Proxy (..))
import Data.Field.Galois (Binary, GaloisField (char, deg, order), Prime)
import Data.Foldable (toList)
import Data.Proxy (asProxyTypeOf)
import Data.Serialize (Serialize, decode, encode)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
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
import Keelung.Compiler.Linker qualified as Linker
import Keelung.Constraint.R1CS (R1CS)
import Keelung.Field
import Keelung.Syntax.Counters
import Keelung.Syntax.Encode.Syntax
import Main.Utf8 (withUtf8)
import Option

type Result n = Either String (R1CS n)

type Result2 n = Either (Error n) (Counters, Vector n, Vector n)

convert :: Integral a => Result a -> Result Integer
convert (Left err) = Left err
convert (Right cs) = Right (fmap toInteger cs)

adapter ::
  (forall n. (KnownNat n) => Result (Prime n) -> IO ()) ->
  (forall n. (KnownNat n) => Result (Binary n) -> IO ()) ->
  (forall n. (KnownNat n) => (FieldType, Int, Integer, Integer) -> Result (Prime n)) ->
  (forall n. (KnownNat n) => (FieldType, Int, Integer, Integer) -> Result (Binary n)) ->
  FieldType ->
  IO ()
adapter funcP _ argP _ (Prime n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) ->
    let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy (Prime n))
        fieldInfo = (Prime n, ceiling (logBase (2 :: Double) (fromIntegral (order fieldNumber))), toInteger (char fieldNumber), toInteger (deg fieldNumber))
     in funcP (argP fieldInfo :: Result (Prime n))
  Nothing -> return ()
adapter _ funcB _ argB (Binary n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) ->
    let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy (Binary n))
        fieldInfo = (Binary n, ceiling (logBase (2 :: Double) (fromIntegral (order fieldNumber))), toInteger (char fieldNumber), toInteger (deg fieldNumber))
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
  (a -> IO ()) ->
  (a -> IO ()) ->
  (forall n. (KnownNat n) => Proxy (Prime n) -> a) ->
  (forall n. (KnownNat n) => Proxy (Binary n) -> a) ->
  FieldType ->
  IO ()
adapter3 funcP _ argP _ (Prime n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) -> funcP (argP (Proxy :: Proxy (Prime n)))
  Nothing -> return ()
adapter3 _ funcB _ argB (Binary n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) -> funcB (argB (Proxy :: Proxy (Binary n)))
  Nothing -> return ()

adapter2 ::
  (forall n. (KnownNat n) => Result2 (Prime n) -> IO ()) ->
  (forall n. (KnownNat n) => Result2 (Binary n) -> IO ()) ->
  (forall n. (KnownNat n) => (FieldType, Int, Integer, Integer) -> Result2 (Prime n)) ->
  (forall n. (KnownNat n) => (FieldType, Int, Integer, Integer) -> Result2 (Binary n)) ->
  FieldType ->
  IO ()
adapter2 funcP _ argP _ (Prime n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) ->
    let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy (Prime n))
        fieldInfo = (Prime n, ceiling (logBase (2 :: Double) (fromIntegral (order fieldNumber))), toInteger (char fieldNumber), toInteger (deg fieldNumber))
     in funcP (argP fieldInfo :: Result2 (Prime n))
  Nothing -> return ()
adapter2 _ funcB _ argB (Binary n) = case someNatVal n of
  Just (SomeNat (_ :: Proxy n)) ->
    let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy (Binary n))
        fieldInfo = (Binary n, ceiling (logBase (2 :: Double) (fromIntegral (order fieldNumber))), toInteger (char fieldNumber), toInteger (deg fieldNumber))
     in funcB (argB fieldInfo :: Result2 (Binary n))
  Nothing -> return ()

-- formFieldInfo :: FieldType -> (FieldType, Int, Integer, Integer)

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
            ( \(Proxy :: Proxy (Prime n)) ->
                Vector.fromList <$> left show (interpretElab elaborated rawPublicInputs rawPrivateInputs :: Either (Error (Prime n)) [Integer])
            )
            ( \(Proxy :: Proxy (Binary n)) ->
                Vector.fromList <$> left show (interpretElab elaborated rawPublicInputs rawPrivateInputs :: Either (Error (Binary n)) [Integer])
            )
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

    outputInterpretedResult :: (Serialize a, Serialize n) => Either a (Vector n) -> IO ()
    outputInterpretedResult = putStrLn . BSC.unpack . encode . fmap toList

    outputInterpretedResultAndWriteFile :: (Serialize n, GaloisField n, Integral n) => FilePath -> Either (Error n) (Counters, Vector n, Vector n) -> IO ()
    outputInterpretedResultAndWriteFile filepath result = do
      case result of
        Left err -> do
          putStrLn $ BSC.unpack $ encode err
        Right (counters, outputs, witness) -> do
          -- print outputs
          putStrLn $ BSC.unpack $ encode $ toList outputs
          -- write files
          BS.writeFile filepath (serializeInputAndWitness counters witness)

run :: (GaloisField n, Integral n) => ExceptT (Error n) IO () -> IO ()
run f = do
  res <- runExceptT f
  case res of
    Left err -> print err
    Right () -> return ()
