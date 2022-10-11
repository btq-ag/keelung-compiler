{-# LANGUAGE DataKinds #-}

module Main where

import Control.Arrow (left)
import Control.Monad.Except
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as BS
import Data.Field.Galois (GaloisField)
import Data.Serialize (Serialize, decode, encode)
import Encode (asJSONLines)
import Keelung.Compiler
  ( ConstraintSystem,
    Error (..),
    compileO0Elab,
    compileO1Elab,
    compileO2Elab,
    interpretElab,
    toR1CS,
  )
import Keelung.Field
import Keelung.Syntax.Typed hiding (elaborate)
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
            B64 -> output (asB64 $ compileO0Elab elaborated)
            GF181 -> output (asGF181 $ compileO0Elab elaborated)
            BN128 -> output (asBN128 $ compileO0Elab elaborated)
    Protocol CompileO1 -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> do
          case fieldType of
            B64 -> output (asB64 $ compileO1Elab elaborated)
            GF181 -> output (asGF181 $ compileO1Elab elaborated)
            BN128 -> output (asBN128 $ compileO1Elab elaborated)
    Protocol CompileO2 -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> do
          case fieldType of
            B64 -> output (asB64 $ compileO2Elab elaborated)
            GF181 -> output (asGF181 $ compileO2Elab elaborated)
            BN128 -> output (asBN128 $ compileO2Elab elaborated)
    Protocol Interpret -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated, [Integer])
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated, inputs) -> do
          case fieldType of
            B64 -> putStrLn $ BSC.unpack $ encode (interpretElab elaborated (map fromInteger inputs) :: Either String [B64])
            GF181 -> putStrLn $ BSC.unpack $ encode (interpretElab elaborated (map fromInteger inputs) :: Either String [GF181])
            BN128 -> putStrLn $ BSC.unpack $ encode (interpretElab elaborated (map fromInteger inputs) :: Either String [BN128])
    Protocol ToJSON -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> do
          case fieldType of
            B64 -> outputAndwriteJSONLines (asB64 $ compileO1Elab elaborated)
            GF181 -> outputAndwriteJSONLines (asGF181 $ compileO1Elab elaborated)
            BN128 -> outputAndwriteJSONLines (asBN128 $ compileO1Elab elaborated)
    Version -> putStrLn "Keelung v0.5.3"
  where
    asB64 :: Either (Error B64) (ConstraintSystem B64) -> Either (Error B64) (ConstraintSystem B64)
    asB64 = id 

    asGF181 :: Either (Error GF181) (ConstraintSystem GF181) -> Either (Error GF181) (ConstraintSystem GF181)
    asGF181 = id

    asBN128 :: Either (Error BN128) (ConstraintSystem BN128) -> Either (Error BN128) (ConstraintSystem BN128)
    asBN128 = id

    output :: (Serialize n, GaloisField n, Integral n) => Either (Error n) (ConstraintSystem n) -> IO ()
    output cs = putStrLn $ BSC.unpack $ encode (left show (toR1CS <$> cs))

    outputAndwriteJSONLines :: (Serialize n, GaloisField n, Integral n) => Either (Error n) (ConstraintSystem n) -> IO ()
    outputAndwriteJSONLines cs = do 
      output cs 
      case cs of 
        Left err -> print err 
        Right cs' -> do
          let r1cs = toR1CS cs'
          BS.writeFile "out.jsonl" (asJSONLines r1cs)

run :: (GaloisField n, Integral n) => ExceptT (Error n) IO () -> IO ()
run f = do
  res <- runExceptT f
  case res of
    Left err -> print err
    Right () -> return ()

