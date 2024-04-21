{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Compilation.Experiment (run, tests) where

import Control.Monad (forM_)
import Data.Either qualified as Either
import Data.Word (Word8)
import Keelung hiding (MulU, VarUI)
import Keelung.Data.U (U)
import Test.Arbitrary (arbitraryUOfWidth)
import Test.Hspec
import Test.QuickCheck
import Test.Util

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Experiment" $ do
  describe "Ordinary Addition" $ do
    it "Byte" $ do
      property $ \(a, b) -> do
        let expected = [(operandToInteger a + operandToInteger b) `mod` 256]
        case (a, b) of
          (Constant valA, Constant valB) -> do
            let program = return $ fromIntegral valA + fromIntegral valB :: Comp (UInt 8)
            check gf181 program [] [] expected
            check (Prime 17) program [] [] expected
            check (Binary 7) program [] [] expected
          (Constant valA, _) -> do
            let program = do
                  y <- input Public :: Comp (UInt 8)
                  return $ fromIntegral valA + y
            check gf181 program [operandToInteger b] [] expected
            check (Prime 17) program [operandToInteger b] [] expected
            check (Binary 7) program [operandToInteger b] [] expected
          (_, Constant valB) -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  return $ x + fromIntegral valB
            check gf181 program [operandToInteger a] [] expected
            check (Prime 17) program [operandToInteger a] [] expected
            check (Binary 7) program [operandToInteger a] [] expected
          _ -> do
            let program = do
                  x <- input Public :: Comp (UInt 8)
                  y <- input Public :: Comp (UInt 8)
                  return $ x + y
            check gf181 program [operandToInteger a, operandToInteger b] [] expected
            check (Prime 17) program [operandToInteger a, operandToInteger b] [] expected
            check (Binary 7) program [operandToInteger a, operandToInteger b] [] expected

  describe "Variable-width Addition" $ do
    it "Byte -> UInt 6" $ do
      property $ \operands -> do
        -- separate constants and variables
        let (constants, vars) = cassifyOperands operands
        let expected = [sum (map operandToInteger (unOperands operands)) `mod` 64]
        let arity = length vars
        let program = do
              xs <- inputList Public arity :: Comp [UInt 8]
              return $ addV (xs <> map fromIntegral constants) :: Comp (UInt 6)
        check gf181 program (map operandToInteger vars) [] expected
        check (Prime 17) program (map operandToInteger vars) [] expected
        check (Binary 7) program (map operandToInteger vars) [] expected

    it "Byte -> UInt 8" $ do
      property $ \operands -> do
        -- separate constants and variables
        let (constants, vars) = cassifyOperands operands
        let expected = [sum (map operandToInteger (unOperands operands)) `mod` 256]
        let arity = length vars
        let program = do
              xs <- inputList Public arity :: Comp [UInt 8]
              return $ addV (xs <> map fromIntegral constants) :: Comp (UInt 8)
        check gf181 program (map operandToInteger vars) [] expected
        check (Prime 17) program (map operandToInteger vars) [] expected
        check (Binary 7) program (map operandToInteger vars) [] expected

    it "Byte -> UInt 10" $ do
        let operands = Operands [NegVar 3]
      -- property $ \operands -> do
        -- separate constants and variables
        let (constants, vars) = cassifyOperands operands
        let expected = [sum (map operandToInteger (unOperands operands)) `mod` 1024]
        let arity = length vars
        let program = do
              xs <- inputList Public arity :: Comp [UInt 8]
              return $ addV (xs <> map fromIntegral constants) :: Comp (UInt 10)
        -- check gf181 program (map operandToInteger vars) [] expected
        -- check (Prime 17) program (map operandToInteger vars) [] expected
        check (Binary 7) program (map operandToInteger vars) [] expected

-- case (a, b) of
--   (Constant valA, Constant valB) -> do
--     let program = return $ addV [fromIntegral valA, fromIntegral valB :: UInt 8] :: Comp (UInt 6)
--     check gf181 program [] [] expected
--     check (Prime 17) program [] [] expected
--     check (Binary 7) program [] [] expected
--   (Constant valA, _) -> do
--     let program = do
--           y <- input Public :: Comp (UInt 8)
--           return $ addV [fromIntegral valA, y] :: Comp (UInt 6)
--     check gf181 program [operandToInteger b] [] expected
--     check (Prime 17) program [operandToInteger b] [] expected
--     check (Binary 7) program [operandToInteger b] [] expected
--   (_, Constant valB) -> do
--     let program = do
--           x <- input Public :: Comp (UInt 8)
--           return $ addV [x, fromIntegral valB] :: Comp (UInt 6)
--     check gf181 program [operandToInteger a] [] expected
--     check (Prime 17) program [operandToInteger a] [] expected
--     check (Binary 7) program [operandToInteger a] [] expected
--   _ -> do
--     let program = do
--           x <- input Public :: Comp (UInt 8)
--           y <- input Public :: Comp (UInt 8)
--           return $ addV [x, y] :: Comp (UInt 6)
--     check gf181 program [operandToInteger a, operandToInteger b] [] expected
--     check (Prime 17) program [operandToInteger a, operandToInteger b] [] expected

-- check gf181 (program (fromIntegral x) (fromIntegral y)) [] [] expected

-- describe "Variable-width addition" $ do
--   it "2 constants / Byte -> UInt 6" $ do
--     let program x y = return $ addV [x, y :: UInt 8] :: Comp (UInt 6)
--     property $ \(x :: Word8, y :: Word8) -> do
--       let expected = [(toInteger x + toInteger y) `mod` 64]
--       check gf181 (program (fromIntegral x) (fromIntegral y)) [] [] expected

--   it "2 constants / Byte -> UInt 9" $ do
--     let program x y = return $ addV [x, y :: UInt 8] :: Comp (UInt 9)
--     property $ \(x :: Word8, y :: Word8) -> do
--       let expected = [(toInteger x + toInteger y) `mod` 512]
--       check gf181 (program (fromIntegral x) (fromIntegral y)) [] [] expected

--   it "2 constants / Byte -> UInt 10" $ do
--     let program x y = return $ addV [x, y :: UInt 8] :: Comp (UInt 10)
--     property $ \(x :: Word8, y :: Word8) -> do
--       let expected = [(toInteger x + toInteger y) `mod` 1024]
--       check gf181 (program (fromIntegral x) (fromIntegral y)) [] [] expected

--   it "2 variables / Byte -> UInt 6" $ do
--     let program n = do
--           xs <- inputList Public n :: Comp [UInt 8]
--           return $ addV xs :: Comp (UInt 6)

--     let genParam = do
--           n <- chooseEnum (0, 10)
--           xs <- vector n
--           return (n, xs)

--     forAll genParam $ \(n, xs :: [Word8]) -> do
--       let expected = [sum (map toInteger xs) `mod` 64]
--       forM_ [gf181, Prime 17, Binary 7] $ \field ->
--         check field (program n) (map toInteger xs) [] expected

--   it "2 variables / Byte -> UInt 10" $ do
--     let program n = do
--           xs <- inputList Public n :: Comp [UInt 8]
--           return $ addV xs :: Comp (UInt 10)
--     let genParam = do
--           n <- chooseEnum (0, 2)
--           xs <- vector n
--           return (n, xs)

--     forAll genParam $ \(n, xs :: [Word8]) -> do
--       let expected = [sum (map toInteger xs) `mod` 1024]
--       forM_ [gf181, Prime 17, Binary 7] $ \field ->
--         check field (program n) (map toInteger xs) [] expected

-- it "1 constant + 1 variable / Byte -> UInt 6" $ do
--   let program x = do
--         y <- input Public :: Comp (UInt 8)
--         return $ x `mulV` y :: Comp (UInt 6)
--   property $ \(x :: Word8, y :: Word8) -> do
--     let expected = [(toInteger x * toInteger y) `mod` 64]
--     check gf181 (program (fromIntegral x)) [toInteger y] [] expected
--     check (Prime 17) (program (fromIntegral x)) [toInteger y] [] expected
--     check (Binary 7) (program (fromIntegral x)) [toInteger y] [] expected

-- it "1 constant + 1 variable / Byte -> UInt 10" $ do
--   let program x = do
--         y <- input Public :: Comp (UInt 8)
--         return $ x `mulV` y :: Comp (UInt 10)
--   property $ \(x :: Word8, y :: Word8) -> do
--     let expected = [(toInteger x * toInteger y) `mod` 1024]
--     check gf181 (program (fromIntegral x)) [toInteger y] [] expected
--     check (Prime 17) (program (fromIntegral x)) [toInteger y] [] expected
--     check (Binary 7) (program (fromIntegral x)) [toInteger y] [] expected

--------------------------------------------------------------------------------

data Operand = Constant U | PosVar U | NegVar U
  deriving (Show)

arbitraryOperandOfWidth :: Width -> Gen Operand
arbitraryOperandOfWidth width =
  oneof
    [ Constant <$> arbitraryUOfWidth width,
      PosVar <$> arbitraryUOfWidth width,
      NegVar <$> arbitraryUOfWidth width
    ]

-- | Default to generating Byte operands
instance Arbitrary Operand where
  arbitrary = arbitraryOperandOfWidth 8

operandToInteger :: Operand -> Integer
operandToInteger (Constant x) = toInteger x
operandToInteger (PosVar x) = toInteger x
operandToInteger (NegVar x) = -toInteger x

--------------------------------------------------------------------------------

newtype Operands = Operands {unOperands :: [Operand]}
  deriving (Show)

instance Arbitrary Operands where
  arbitrary = do
    n <- chooseInt (0, 10)
    Operands <$> vector n

cassifyOperands :: Operands -> ([U], [Operand])
cassifyOperands = Either.partitionEithers . map cassifyOperand . unOperands
  where
    cassifyOperand :: Operand -> Either U Operand
    cassifyOperand (Constant x) = Left x
    cassifyOperand x = Right x