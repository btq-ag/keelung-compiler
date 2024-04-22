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
  it "failed" $ do
    let program = do
          y <- input Public :: Comp (UInt 8)
          return $ 1 * (-y)
    -- debug (Binary 7) program 
    check (Binary 7) program [10] [] [246]
  -- describe "Ordinary Multiplication" $ do
  --   it "Byte" $ do
  --     property $ \(a, b) -> do
  --       let expected = [(operandToSignedInteger a * operandToSignedInteger b) `mod` 256]
  --       case (a, b) of
  --         (Constant valA, Constant valB) -> do
  --           let program = return $ fromIntegral valA * fromIntegral valB :: Comp (UInt 8)
  --           check gf181 program [] [] expected
  --           check (Prime 17) program [] [] expected
  --           check (Binary 7) program [] [] expected
  --         (Constant valA, _) -> do
  --           let program = do
  --                 y <- input Public :: Comp (UInt 8)
  --                 return $ fromIntegral valA * operandToSignedVariable b y
  --           check gf181 program [operandToUnsignedInteger b] [] expected
  --           check (Prime 17) program [operandToUnsignedInteger b] [] expected
  --         -- check (Binary 7) program [operandToUnsignedInteger b] [] expected
  --         (_, Constant valB) -> do
  --           let program = do
  --                 x <- input Public :: Comp (UInt 8)
  --                 return $ operandToSignedVariable a x * fromIntegral valB
  --           check gf181 program [operandToUnsignedInteger a] [] expected
  --           check (Prime 17) program [operandToUnsignedInteger a] [] expected
  --         -- check (Binary 7) program [operandToUnsignedInteger a] [] expected
  --         _ -> do
  --           let program = do
  --                 x <- input Public :: Comp (UInt 8)
  --                 y <- input Public :: Comp (UInt 8)
  --                 return $ operandToSignedVariable a x * operandToSignedVariable b y
  --           check gf181 program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
  --           check (Prime 17) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
  --           check (Binary 7) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected

-- describe "Variable-width Multiplication" $ do
--   it "Byte -> UInt 6" $ do
--     property $ \(a, b) -> do
--       let expected = [(operandToSignedInteger a * operandToSignedInteger b) `mod` 64]
--       case (a, b) of
--         (Constant valA, Constant valB) -> do
--           let program = return $ (fromIntegral valA :: UInt 8) `mulV` fromIntegral valB :: Comp (UInt 6)
--           check gf181 program [] [] expected
--           check (Prime 17) program [] [] expected
--           check (Binary 7) program [] [] expected
--         (Constant valA, _) -> do
--           let program = do
--                 y <- input Public :: Comp (UInt 8)
--                 return $ fromIntegral valA `mulV` y :: Comp (UInt 6)
--           check gf181 program [operandToUnsignedInteger b] [] expected
--           check (Prime 17) program [operandToUnsignedInteger b] [] expected
--           check (Binary 7) program [operandToUnsignedInteger b] [] expected
--         (_, Constant valB) -> do
--           let program = do
--                 x <- input Public :: Comp (UInt 8)
--                 return $ x `mulV` fromIntegral valB :: Comp (UInt 6)
--           check gf181 program [operandToUnsignedInteger a] [] expected
--           check (Prime 17) program [operandToUnsignedInteger a] [] expected
--           check (Binary 7) program [operandToUnsignedInteger a] [] expected
--         _ -> do
--           let program = do
--                 x <- input Public :: Comp (UInt 8)
--                 y <- input Public :: Comp (UInt 8)
--                 return $ x `mulV` y :: Comp (UInt 6)
--           check gf181 program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
--           check (Prime 17) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
--           check (Binary 7) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
--   it "Byte -> UInt 8" $ do
--     property $ \(a, b) -> do
--       let expected = [(operandToSignedInteger a * operandToSignedInteger b) `mod` 256]
--       case (a, b) of
--         (Constant valA, Constant valB) -> do
--           let program = return $ (fromIntegral valA :: UInt 8) `mulV` fromIntegral valB :: Comp (UInt 8)
--           check gf181 program [] [] expected
--           check (Prime 17) program [] [] expected
--           check (Binary 7) program [] [] expected
--         (Constant valA, _) -> do
--           let program = do
--                 y <- input Public :: Comp (UInt 8)
--                 return $ fromIntegral valA `mulV` y :: Comp (UInt 8)
--           check gf181 program [operandToUnsignedInteger b] [] expected
--           check (Prime 17) program [operandToUnsignedInteger b] [] expected
--           check (Binary 7) program [operandToUnsignedInteger b] [] expected
--         (_, Constant valB) -> do
--           let program = do
--                 x <- input Public :: Comp (UInt 8)
--                 return $ x `mulV` fromIntegral valB :: Comp (UInt 8)
--           check gf181 program [operandToUnsignedInteger a] [] expected
--           check (Prime 17) program [operandToUnsignedInteger a] [] expected
--           check (Binary 7) program [operandToUnsignedInteger a] [] expected
--         _ -> do
--           let program = do
--                 x <- input Public :: Comp (UInt 8)
--                 y <- input Public :: Comp (UInt 8)
--                 return $ x `mulV` y :: Comp (UInt 8)
--           check gf181 program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
--           check (Prime 17) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
--           check (Binary 7) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
--   it "Byte -> UInt 10" $ do
--     property $ \(a, b) -> do
--       let expected = [(operandToSignedInteger a * operandToSignedInteger b) `mod` 1024]
--       case (a, b) of
--         (Constant valA, Constant valB) -> do
--           let program = return $ (fromIntegral valA :: UInt 8) `mulV` fromIntegral valB :: Comp (UInt 10)
--           check gf181 program [] [] expected
--           check (Prime 17) program [] [] expected
--           check (Binary 7) program [] [] expected
--         (Constant valA, _) -> do
--           let program = do
--                 y <- input Public :: Comp (UInt 8)
--                 return $ fromIntegral valA `mulV` y :: Comp (UInt 10)
--           check gf181 program [operandToUnsignedInteger b] [] expected
--           check (Prime 17) program [operandToUnsignedInteger b] [] expected
--           check (Binary 7) program [operandToUnsignedInteger b] [] expected
--         (_, Constant valB) -> do
--           let program = do
--                 x <- input Public :: Comp (UInt 8)
--                 return $ x `mulV` fromIntegral valB :: Comp (UInt 10)
--           check gf181 program [operandToUnsignedInteger a] [] expected
--           check (Prime 17) program [operandToUnsignedInteger a] [] expected
--           check (Binary 7) program [operandToUnsignedInteger a] [] expected
--         _ -> do
--           let program = do
--                 x <- input Public :: Comp (UInt 8)
--                 y <- input Public :: Comp (UInt 8)
--                 return $ x `mulV` y :: Comp (UInt 10)
--           check gf181 program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
--           check (Prime 17) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
--           check (Binary 7) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
-- describe "Double-width Multiplication" $ do
--   it "UInt 8 -> UInt 16" $ do
--     property $ \(a, b) -> do
--       let expected = [(operandToSignedInteger a * operandToSignedInteger b) `mod` 65536]
--       case (a, b) of
--         (Constant valA, Constant valB) -> do
--           let program = return $ (fromIntegral valA :: UInt 8) `mulD` fromIntegral valB :: Comp (UInt 16)
--           check gf181 program [] [] expected
--           check (Prime 17) program [] [] expected
--           check (Binary 7) program [] [] expected
--         (Constant valA, _) -> do
--           let program = do
--                 y <- input Public :: Comp (UInt 8)
--                 return $ fromIntegral valA `mulD` y :: Comp (UInt 16)
--           check gf181 program [operandToUnsignedInteger b] [] expected
--           check (Prime 17) program [operandToUnsignedInteger b] [] expected
--           check (Binary 7) program [operandToUnsignedInteger b] [] expected
--         (_, Constant valB) -> do
--           let program = do
--                 x <- input Public :: Comp (UInt 8)
--                 return $ x `mulD` fromIntegral valB :: Comp (UInt 16)
--           check gf181 program [operandToUnsignedInteger a] [] expected
--           check (Prime 17) program [operandToUnsignedInteger a] [] expected
--           check (Binary 7) program [operandToUnsignedInteger a] [] expected
--         _ -> do
--           let program = do
--                 x <- input Public :: Comp (UInt 8)
--                 y <- input Public :: Comp (UInt 8)
--                 return $ x `mulD` y :: Comp (UInt 16)
--           check gf181 program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
--           check (Prime 17) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
--           check (Binary 7) program [operandToUnsignedInteger a, operandToUnsignedInteger b] [] expected
