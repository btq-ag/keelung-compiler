{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Compilation.Experiment (run, tests) where

import Control.Monad (forM_)
import Data.Either qualified as Either
import Data.Word (Word8)
import Keelung hiding (MulU, VarUI)
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Test.Arbitrary (arbitraryUOfWidth)
import Test.Hspec
import Test.QuickCheck
import Test.Util

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Experiment" $ do
  describe "Ordinary Multiplication" $ do
    it "Byte" $ do
      property $ \(a, b) -> do
        let expected = [(operandToInteger a * operandToInteger b) `mod` 256]
        case (a, b) of
          (Constant valA, Constant valB) -> do
            let program = return $ fromIntegral valA * fromIntegral valB :: Comp (UInt 8)
            check gf181 program [] [] expected
            check (Prime 17) program [] [] expected
            check (Binary 7) program [] [] expected
          (Constant valA, _) -> do
            let program = do
                  y <- input Public :: Comp (UInt 8)
                  return $ fromIntegral valA * y
            check gf181 program [operandToInteger b] [] expected
            check (Prime 17) program [operandToInteger b] [] expected
            check (Binary 7) program [operandToInteger b] [] expected
          (_, Constant valB) -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  return $ x * fromIntegral valB
            check gf181 program [operandToInteger a] [] expected
            check (Prime 17) program [operandToInteger a] [] expected
            check (Binary 7) program [operandToInteger a] [] expected
          _ -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  y <- input Public :: Comp (UInt 8)
                  return $ x * y
            check gf181 program [operandToInteger a, operandToInteger b] [] expected
            check (Prime 17) program [operandToInteger a, operandToInteger b] [] expected
            check (Binary 7) program [operandToInteger a, operandToInteger b] [] expected

  describe "Variable-width Multiplication" $ do
    it "Byte -> UInt 6" $ do
      property $ \(a, b) -> do
        let expected = [(operandToInteger a * operandToInteger b) `mod` 64]
        case (a, b) of
          (Constant valA, Constant valB) -> do
            let program = return $ (fromIntegral valA :: UInt 8) `mulV` fromIntegral valB :: Comp (UInt 6)
            check gf181 program [] [] expected
            check (Prime 17) program [] [] expected
            check (Binary 7) program [] [] expected
          (Constant valA, _) -> do
            let program = do
                  y <- input Public :: Comp (UInt 8)
                  return $ fromIntegral valA `mulV` y :: Comp (UInt 6)
            check gf181 program [operandToInteger b] [] expected
            check (Prime 17) program [operandToInteger b] [] expected
            check (Binary 7) program [operandToInteger b] [] expected
          (_, Constant valB) -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  return $ x `mulV` fromIntegral valB :: Comp (UInt 6)
            check gf181 program [operandToInteger a] [] expected
            check (Prime 17) program [operandToInteger a] [] expected
            check (Binary 7) program [operandToInteger a] [] expected
          _ -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  y <- input Public :: Comp (UInt 8)
                  return $ x `mulV` y :: Comp (UInt 6)
            check gf181 program [operandToInteger a, operandToInteger b] [] expected
            check (Prime 17) program [operandToInteger a, operandToInteger b] [] expected
            check (Binary 7) program [operandToInteger a, operandToInteger b] [] expected
    it "Byte -> UInt 8" $ do
      property $ \(a, b) -> do
        let expected = [(operandToInteger a * operandToInteger b) `mod` 256]
        case (a, b) of
          (Constant valA, Constant valB) -> do
            let program = return $ (fromIntegral valA :: UInt 8) `mulV` fromIntegral valB :: Comp (UInt 8)
            check gf181 program [] [] expected
            check (Prime 17) program [] [] expected
            check (Binary 7) program [] [] expected
          (Constant valA, _) -> do
            let program = do
                  y <- input Public :: Comp (UInt 8)
                  return $ fromIntegral valA `mulV` y :: Comp (UInt 8)
            check gf181 program [operandToInteger b] [] expected
            check (Prime 17) program [operandToInteger b] [] expected
            check (Binary 7) program [operandToInteger b] [] expected
          (_, Constant valB) -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  return $ x `mulV` fromIntegral valB :: Comp (UInt 8)
            check gf181 program [operandToInteger a] [] expected
            check (Prime 17) program [operandToInteger a] [] expected
            check (Binary 7) program [operandToInteger a] [] expected
          _ -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  y <- input Public :: Comp (UInt 8)
                  return $ x `mulV` y :: Comp (UInt 8)
            check gf181 program [operandToInteger a, operandToInteger b] [] expected
            check (Prime 17) program [operandToInteger a, operandToInteger b] [] expected
            check (Binary 7) program [operandToInteger a, operandToInteger b] [] expected
    it "Byte -> UInt 10" $ do
      property $ \(a, b) -> do
        let expected = [(operandToInteger a * operandToInteger b) `mod` 1024]
        case (a, b) of
          (Constant valA, Constant valB) -> do
            let program = return $ (fromIntegral valA :: UInt 8) `mulV` fromIntegral valB :: Comp (UInt 10)
            check gf181 program [] [] expected
            check (Prime 17) program [] [] expected
            check (Binary 7) program [] [] expected
          (Constant valA, _) -> do
            let program = do
                  y <- input Public :: Comp (UInt 8)
                  return $ fromIntegral valA `mulV` y :: Comp (UInt 10)
            check gf181 program [operandToInteger b] [] expected
            check (Prime 17) program [operandToInteger b] [] expected
            check (Binary 7) program [operandToInteger b] [] expected
          (_, Constant valB) -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  return $ x `mulV` fromIntegral valB :: Comp (UInt 10)
            check gf181 program [operandToInteger a] [] expected
            check (Prime 17) program [operandToInteger a] [] expected
            check (Binary 7) program [operandToInteger a] [] expected
          _ -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  y <- input Public :: Comp (UInt 8)
                  return $ x `mulV` y :: Comp (UInt 10)
            check gf181 program [operandToInteger a, operandToInteger b] [] expected
            check (Prime 17) program [operandToInteger a, operandToInteger b] [] expected
            check (Binary 7) program [operandToInteger a, operandToInteger b] [] expected
  describe "Double-width Multiplication" $ do 
    it "UInt 8 -> UInt 16" $ do
      property $ \(a, b) -> do
        let expected = [(operandToInteger a * operandToInteger b) `mod` 65536]
        case (a, b) of
          (Constant valA, Constant valB) -> do
            let program = return $ (fromIntegral valA :: UInt 8) `mulD` fromIntegral valB :: Comp (UInt 16)
            check gf181 program [] [] expected
            check (Prime 17) program [] [] expected
            check (Binary 7) program [] [] expected
          (Constant valA, _) -> do
            let program = do
                  y <- input Public :: Comp (UInt 8)
                  return $ fromIntegral valA `mulD` y :: Comp (UInt 16)
            check gf181 program [operandToInteger b] [] expected
            check (Prime 17) program [operandToInteger b] [] expected
            check (Binary 7) program [operandToInteger b] [] expected
          (_, Constant valB) -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  return $ x `mulD` fromIntegral valB :: Comp (UInt 16)
            check gf181 program [operandToInteger a] [] expected
            check (Prime 17) program [operandToInteger a] [] expected
            check (Binary 7) program [operandToInteger a] [] expected
          _ -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  y <- input Public :: Comp (UInt 8)
                  return $ x `mulD` y :: Comp (UInt 16)
            check gf181 program [operandToInteger a, operandToInteger b] [] expected
            check (Prime 17) program [operandToInteger a, operandToInteger b] [] expected
            check (Binary 7) program [operandToInteger a, operandToInteger b] [] expected
