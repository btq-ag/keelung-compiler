module Keelung.Compiler.Compile.UInt.Bitwise (compileShiftL, compileRotateL, compileSetBit, compileBtoU) where

import Control.Monad
import Data.Bits qualified
import Data.Field.Galois
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice (Slice))
import Keelung.Data.U (U)

-- | Compile a shift left operation
compileShiftL :: (GaloisField n, Integral n) => Width -> RefU -> Int -> Either RefU U -> M n ()
compileShiftL width out n (Left var) = do
  case compare n 0 of
    EQ -> writeSliceEq (Slice out 0 width) (Slice var 0 width)
    GT -> do
      let n' = n `min` width
      -- fill lower bits with 0s
      writeSliceVal (Slice out 0 n') 0
      -- shift upper bits
      writeSliceEq (Slice out n' width) (Slice var 0 (width - n'))
    LT -> do
      let n' = n `max` (-width)
      -- shift lower bits
      writeSliceEq (Slice out 0 (width + n')) (Slice var (-n') width)
      -- fill upper bits with 0s
      writeSliceVal (Slice out (width + n') width) 0
compileShiftL width out n (Right val) = do
  case compare n 0 of
    EQ -> writeSliceVal (Slice out 0 width) (toInteger val)
    GT -> writeSliceVal (Slice out 0 width) (toInteger (val `Data.Bits.shiftL` n))
    LT -> writeSliceVal (Slice out 0 width) (toInteger (val `Data.Bits.shiftR` (-n)))

-- | Compile a rotate left operation
compileRotateL :: (GaloisField n, Integral n) => Width -> RefU -> Int -> Either RefU U -> M n ()
compileRotateL width out n (Left var) = do
  forM_ [0 .. width - 1] $ \i -> do
    let i' = (i - n) `mod` width
    writeRefBEq (RefUBit out i) (RefUBit var i') -- out[i] = x[i']
compileRotateL width out n (Right val) = do
  forM_ [0 .. width - 1] $ \i -> do
    let i' = (i - n) `mod` width
    writeRefBVal (RefUBit out i) (Data.Bits.testBit val i') -- out[i] = val[i']

-- | Compile a set bit operation
compileSetBit :: (GaloisField n, Integral n) => Width -> RefU -> Int -> Either RefU U -> Either RefB Bool -> M n ()
compileSetBit width out j lhs rhs = do
  forM_ [0 .. width - 1] $ \i -> do
    if i == j
      then case rhs of
        Left var -> writeRefBEq (RefUBit out i) var
        Right val -> writeRefBVal (RefUBit out i) val
      else do
        case lhs of
          Left var -> writeRefBEq (RefUBit out i) (RefUBit var i) -- out[i] = x'[i]
          Right val -> writeRefBVal (RefUBit out i) (Data.Bits.testBit val i) -- out[i] = x'[i]

-- | Compile a Boolean to UInt operation
compileBtoU :: (GaloisField n, Integral n) => Width -> RefU -> Either RefB Bool -> M n ()
compileBtoU width out (Left var) = do
  -- 1. wire 'out[ZERO]' to 'x'
  writeRefBEq (RefUBit out 0) var -- out[0] = x
  -- 2. wire 'out[SUCC _]' to '0' for all other bits
  forM_ [1 .. width - 1] $ \i ->
    writeRefBVal (RefUBit out i) False -- out[i] = 0
compileBtoU width out (Right val) = do
  -- 1. wire 'out[ZERO]' to 'x'
  writeRefBVal (RefUBit out 0) val -- out[0] = x
  -- 2. wire 'out[SUCC _]' to '0' for all other bits
  forM_ [1 .. width - 1] $ \i ->
    writeRefBVal (RefUBit out i) False -- out[i] = 0