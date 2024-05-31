{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Addition (tests, run) where

import Keelung hiding (compile)
import Test.Compilation.UInt.Addition.LimbBound qualified as LimbBound
import Test.Hspec
import Test.QuickCheck
import Test.Util

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Addition / Subtraction" $ do
  LimbBound.tests
  describe "Ordinary Addition" $ do
    it "Byte" $ do
      property $ \(a, b) -> do
        let expected = [(operandToSignedInteger a + operandToSignedInteger b) `mod` 256]
        case (a, b) of
          (Constant valA, Constant valB) -> do
            let program = return $ fromIntegral valA + fromIntegral valB :: Comp (UInt 8)
            check gf181 program [] [] expected
            check (Prime 17) program [] [] expected
            check (Binary 7) program [] [] expected
          (Constant valA, PosVar _) -> do
            let program = do
                  y <- input Public :: Comp (UInt 8)
                  return $ fromIntegral valA + y
            check gf181 program [operandToUnsignedInteger b] [] expected
            check (Prime 17) program [operandToUnsignedInteger b] [] expected
            check (Binary 7) program [operandToUnsignedInteger b] [] expected
          (Constant valA, NegVar _) -> do
            let program = do
                  y <- input Public :: Comp (UInt 8)
                  return $ fromIntegral valA - y
            check gf181 program [operandToUnsignedInteger b] [] expected
            check (Prime 17) program [operandToUnsignedInteger b] [] expected
            check (Binary 7) program [operandToUnsignedInteger b] [] expected
          (PosVar _, Constant valB) -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  return $ x + fromIntegral valB
            check gf181 program [operandToUnsignedInteger a] [] expected
            check (Prime 17) program [operandToUnsignedInteger a] [] expected
            check (Binary 7) program [operandToUnsignedInteger a] [] expected
          (NegVar _, Constant valB) -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  return $ -x + fromIntegral valB
            check gf181 program [operandToUnsignedInteger a] [] expected
            check (Prime 17) program [operandToUnsignedInteger a] [] expected
            check (Binary 7) program [operandToUnsignedInteger a] [] expected
          (PosVar _, PosVar _) -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  y <- input Public :: Comp (UInt 8)
                  return $ x + y
            check gf181 program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
            check (Prime 17) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
            check (Binary 7) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
          (PosVar _, NegVar _) -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  y <- input Public :: Comp (UInt 8)
                  return $ x - y
            check gf181 program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
            check (Prime 17) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
            check (Binary 7) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
          (NegVar _, PosVar _) -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  y <- input Public :: Comp (UInt 8)
                  return $ -x + y
            check gf181 program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
            check (Prime 17) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
            check (Binary 7) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
          (NegVar _, NegVar _) -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  y <- input Public :: Comp (UInt 8)
                  return $ -x - y
            check gf181 program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
            check (Prime 17) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
            check (Binary 7) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected

  describe "Variable-width Addition" $ do
    it "Byte -> UInt 6" $ do
      property $ \operands -> do
        -- separate constants and variables
        let (constants, vars) = cassifyOperands operands
        let expected = [sum (map operandToSignedInteger (unOperands operands)) `mod` 64]
        let arity = length vars
        let program = do
              xs <- inputList Public arity :: Comp [UInt 8]
              let xs' = zipWith operandToSignedVariable vars xs
              return $ addV (xs' <> map fromIntegral constants) :: Comp (UInt 6)
        check gf181 program (map operandToUnsignedInteger vars) [] expected
        check (Prime 17) program (map operandToUnsignedInteger vars) [] expected
        check (Binary 7) program (map operandToUnsignedInteger vars) [] expected

    it "Byte -> UInt 8" $ do
      property $ \operands -> do
        -- separate constants and variables
        let (constants, vars) = cassifyOperands operands
        let expected = [sum (map operandToSignedInteger (unOperands operands)) `mod` 256]
        let arity = length vars
        let program = do
              xs <- inputList Public arity :: Comp [UInt 8]
              let xs' = zipWith operandToSignedVariable vars xs
              return $ addV (xs' <> map fromIntegral constants) :: Comp (UInt 8)
        check gf181 program (map operandToUnsignedInteger vars) [] expected
        check (Prime 17) program (map operandToUnsignedInteger vars) [] expected
        check (Binary 7) program (map operandToUnsignedInteger vars) [] expected

    it "Byte -> UInt 10" $ do
      property $ \operands -> do
        -- separate constants and variables
        let (constants, vars) = cassifyOperands operands
        let expected = [sum (map operandToSignedInteger (unOperands operands)) `mod` 1024]
        let arity = length vars
        let program = do
              xs <- inputList Public arity :: Comp [UInt 8]
              let xs' = zipWith operandToSignedVariable vars xs
              return $ addV (xs' <> map fromIntegral constants) :: Comp (UInt 10)
        check gf181 program (map operandToUnsignedInteger vars) [] expected
        check (Prime 17) program (map operandToUnsignedInteger vars) [] expected
        check (Binary 7) program (map operandToUnsignedInteger vars) [] expected
