module Keelung.Compiler.Compile.UInt.Bitwise (compileShiftL, compileRotateL, compileSetBit, compileBtoU) where

import Control.Monad
import Data.Bits qualified
import Data.Field.Galois
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.Reference
import Keelung.Data.U (U)

-- | Compile a shift left operation
compileShiftL :: (GaloisField n, Integral n) => Width -> RefU -> Int -> Either RefU U -> M n ()
compileShiftL width out n (Left var) = do
  case compare n 0 of
    EQ -> writeRefUEq out var
    GT -> do
      -- fill lower bits with 0s
      forM_ [0 .. n - 1] $ \i -> do
        writeRefBVal (RefUBit width out i) False -- out[i] = 0
        -- shift upper bits
      forM_ [n .. width - 1] $ \i -> do
        let i' = (i - n) `mod` width
        writeRefBEq (RefUBit width out i) (RefUBit width var i') -- out[i] = x'[i']
    LT -> do
      -- shift lower bits
      forM_ [0 .. width + n - 1] $ \i -> do
        let i' = (i - n) `mod` width
        writeRefBEq (RefUBit width out i) (RefUBit width var i') -- out[i] = x'[i']
        -- fill upper bits with 0s
      forM_ [width + n .. width - 1] $ \i -> do
        writeRefBVal (RefUBit width out i) False -- out[i] = 0
compileShiftL width out n (Right val) = do
  case compare n 0 of
    EQ -> writeRefUVal out val
    GT -> do
      -- fill lower bits with 0s
      forM_ [0 .. n - 1] $ \i -> do
        writeRefBVal (RefUBit width out i) False -- out[i] = 0
        -- shift upper bits
      forM_ [n .. width - 1] $ \i -> do
        let i' = (i - n) `mod` width
        writeRefBVal (RefUBit width out i) (Data.Bits.testBit val i') -- out[i] = x'[i']
    LT -> do
      -- shift lower bits
      forM_ [0 .. width + n - 1] $ \i -> do
        let i' = (i - n) `mod` width
        writeRefBVal (RefUBit width out i) (Data.Bits.testBit val i') -- out[i] = x'[i']
        -- fill upper bits with 0s
      forM_ [width + n .. width - 1] $ \i -> do
        writeRefBVal (RefUBit width out i) False -- out[i] = 0

-- | Compile a rotate left operation
compileRotateL :: (GaloisField n, Integral n) => Width -> RefU -> Int -> Either RefU U -> M n ()
compileRotateL width out n (Left var) = do
  forM_ [0 .. width - 1] $ \i -> do
    let i' = (i - n) `mod` width
    writeRefBEq (RefUBit width out i) (RefUBit width var i') -- out[i] = x[i']
compileRotateL width out n (Right val) = do
  forM_ [0 .. width - 1] $ \i -> do
    let i' = (i - n) `mod` width
    writeRefBVal (RefUBit width out i) (Data.Bits.testBit val i') -- out[i] = val[i']

-- | Compile a set bit operation
compileSetBit :: (GaloisField n, Integral n) => Width -> RefU -> Int -> Either RefU U -> Either RefB Bool -> M n ()
compileSetBit width out j lhs rhs = do
  forM_ [0 .. width - 1] $ \i -> do
    if i == j
      then case rhs of
        Left var -> writeRefBEq (RefUBit width out i) var
        Right val -> writeRefBVal (RefUBit width out i) val
      else do
        case lhs of
          Left var -> writeRefBEq (RefUBit width out i) (RefUBit width var i) -- out[i] = x'[i]
          Right val -> writeRefBVal (RefUBit width out i) (Data.Bits.testBit val i) -- out[i] = x'[i]

-- | Compile a Boolean to UInt operation
compileBtoU :: (GaloisField n, Integral n) => Width -> RefU -> Either RefB Bool -> M n ()
compileBtoU width out (Left var) = do
  -- 1. wire 'out[ZERO]' to 'x'
  writeRefBEq (RefUBit width out 0) var -- out[0] = x
  -- 2. wire 'out[SUCC _]' to '0' for all other bits
  forM_ [1 .. width - 1] $ \i ->
    writeRefBVal (RefUBit width out i) False -- out[i] = 0
compileBtoU width out (Right val) = do
  -- 1. wire 'out[ZERO]' to 'x'
  writeRefBVal (RefUBit width out 0) val -- out[0] = x
  -- 2. wire 'out[SUCC _]' to '0' for all other bits
  forM_ [1 .. width - 1] $ \i ->
    writeRefBVal (RefUBit width out i) False -- out[i] = 0