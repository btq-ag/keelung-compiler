{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use head" #-}
module Keelung.Compiler.Compile.UInt.AESMul (compileAESMulU) where

import Control.Monad
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.Word (Word8)
import Keelung.Compiler.Compile.Boolean qualified as Boolean
import Keelung.Compiler.Compile.Monad
import Keelung.Data.Reference
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U

--------------------------------------------------------------------------------

-- | GF(256) multiplication for AES
--   See https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf for more
compileAESMulU :: (GaloisField n, Integral n) => RefU -> Either RefU U -> Either RefU U -> M n ()
compileAESMulU out (Right a) (Right b) = writeRefUVal out (U.aesMul a b)
compileAESMulU out (Right a) (Left b) = compileAESMulCV out a b
compileAESMulU out (Left a) (Right b) = compileAESMulCV out b a
compileAESMulU out (Left a) (Left b) = compileAESMulCC out a b

-- | The specialization of `aesMul 2` can be expressed as a shift and a xor with 0x1b like this:
--
--      input  = [b0, b1, b2, b3, b4, b5, b6, b7]
--      output = [b7, b0 ⊕ b7, b1, b2 ⊕ b7, b3 ⊕ b7, b4, b5, b6]
--
--   `aesMul 4` can be calculated by applying `aesMul 2` twice.
--   With this in mind, we can rewrite `aesMul c` for any constant `c` as the sum of these repeated applications

-- | We use a Word8 to represent the occurence of input bits to be XORed
--   For example, `aesMul 1` can be represented as:
--      (0b00000001, 0b00000010, 0b00000100, 0b00001000, 0b00010000, 0b00100000, 0b01000000, 0b10000000)
--   while `aesMul 2` can be represented as:
--      (0b10000000, 0b10000001, 0b00000010, 0b10000100, 0b10001000, 0b00010000, 0b00100000, 0b01000000)
type XorCode = (Word8, Word8, Word8, Word8, Word8, Word8, Word8, Word8)

compileAESMulCV :: (GaloisField n, Integral n) => RefU -> U -> RefU -> M n ()
compileAESMulCV out c x = do
  let (code0, code1, code2, code3, code4, code5, code6, code7) = calculateXorCode (toInteger c)
  Boolean.xorBs (codeToXors x code0) >>= writeRefB (RefUBit out 0)
  Boolean.xorBs (codeToXors x code1) >>= writeRefB (RefUBit out 1)
  Boolean.xorBs (codeToXors x code2) >>= writeRefB (RefUBit out 2)
  Boolean.xorBs (codeToXors x code3) >>= writeRefB (RefUBit out 3)
  Boolean.xorBs (codeToXors x code4) >>= writeRefB (RefUBit out 4)
  Boolean.xorBs (codeToXors x code5) >>= writeRefB (RefUBit out 5)
  Boolean.xorBs (codeToXors x code6) >>= writeRefB (RefUBit out 6)
  Boolean.xorBs (codeToXors x code7) >>= writeRefB (RefUBit out 7)
  where
    -- \| Derive the XorCode for a constant
    calculateXorCode :: Integer -> XorCode
    calculateXorCode 0 = (0, 0, 0, 0, 0, 0, 0, 0)
    calculateXorCode 1 = (1, 2, 4, 8, 16, 32, 64, 128)
    calculateXorCode 2 = (128, 129, 2, 132, 136, 16, 32, 64)
    calculateXorCode 4 = (64, 192, 129, 66, 196, 136, 16, 32)
    calculateXorCode 8 = (32, 96, 192, 161, 98, 196, 136, 16)
    calculateXorCode 16 = (16, 48, 96, 208, 177, 98, 196, 136)
    calculateXorCode 32 = (136, 152, 48, 232, 88, 177, 98, 196)
    calculateXorCode 64 = (196, 76, 152, 244, 44, 88, 177, 98)
    calculateXorCode 128 = (98, 166, 76, 250, 150, 44, 88, 177)
    calculateXorCode n = double (calculateXorCode (n `div` 2)) `add` calculateXorCode (n `mod` 2)
      where
        double :: XorCode -> XorCode
        double (b0, b1, b2, b3, b4, b5, b6, b7) = (b7, b0 `Data.Bits.xor` b7, b1, b2 `Data.Bits.xor` b7, b3 `Data.Bits.xor` b7, b4, b5, b6)

        add :: XorCode -> XorCode -> XorCode
        add (b0, b1, b2, b3, b4, b5, b6, b7) (b0', b1', b2', b3', b4', b5', b6', b7') =
          ( b0 `Data.Bits.xor` b0',
            b1 `Data.Bits.xor` b1',
            b2 `Data.Bits.xor` b2',
            b3 `Data.Bits.xor` b3',
            b4 `Data.Bits.xor` b4',
            b5 `Data.Bits.xor` b5',
            b6 `Data.Bits.xor` b6',
            b7 `Data.Bits.xor` b7'
          )

    -- \| Generate a list of bits to be XORed from a Word8
    codeToXors :: RefU -> Word8 -> [Either RefB Bool]
    codeToXors ref code = [Left (RefUBit ref i) | i <- [0 .. 7], Data.Bits.testBit code i]

--  Each of the numbers inside the following list are of Word8
--  for representing which bits of x to be XORed
--
--  XOR with y[0]: [  1,   2,   4,   8,  16,  32,  64, 128]
--  XOR with y[1]: [128, 129,   2, 132, 136,  16,  32,  64]
--  XOR with y[2]: [ 64, 192, 129,  66, 196, 136,  16,  32]
--  XOR with y[3]: [ 32,  96, 192, 161,  98, 196, 136,  16]
--  XOR with y[4]: [ 16,  48,  96, 208, 177,  98, 196, 136]
--  XOR with y[5]: [136, 152,  48, 232,  88, 177,  98, 196]
--  XOR with y[6]: [196,  76, 152, 244,  44,  88, 177,  98]
--  XOR with y[7]: [ 98, 166,  76, 250, 150,  44,  88, 177]
--
--  notation in the following comment:
--    192 # y[2] => 0b11000000 # y[2] => (x[7] ⊕ x[6])y[2]
--    161 # y[3] => 0b10100001 # y[3] => (x[7] ⊕ x[5] ⊕ x[2])y[3]
--    208 # y[4] => 0b11010000 # y[4] => (x[7] ⊕ x[6] ⊕ x[4])y[4]
compileAESMulCC :: (GaloisField n, Integral n) => RefU -> RefU -> RefU -> M n ()
compileAESMulCC out x y = do
  -- products of x and y
  products <- forM [0 .. 7] $ \i -> do
    forM [0 .. 7] $ \j -> do
      let xBit = RefUBit x i
      let yBit = RefUBit y j
      Boolean.andBs [Left xBit, Left yBit]
  -- out[0] = 1 # y[0] ⊕ 128 # y[1] ⊕ 64 # y[2] ⊕ 32 # y[3] ⊕ 16 # y[4] ⊕ 136 # y[5] ⊕ 196 # y[6] ⊕ 98 # y[7]
  --        = 0b00000001 # y[0] ⊕ 0b10000000 # y[1] ⊕ 0b01000000 # y[2] ⊕ 0b00100000 # y[3] ⊕ 0b00010000 # y[4] ⊕ 0b10001000 # y[5] ⊕ 0b11000100 # y[6] ⊕ 0b01100010 # y[7]
  --        = (x[0])y[0] ⊕ (x[7])y[1] ⊕ (x[6])y[2] ⊕ (x[5])y[3] ⊕ (x[4])y[4] ⊕ (x[7] ⊕ x[3])y[5] ⊕ (x[7] ⊕ x[6] ⊕ x[2])y[6] ⊕ (x[6] ⊕ x[5] ⊕ x[1])y[7]
  writeRefB (RefUBit out 0)
    =<< Boolean.xorBs
      [ products !! 0 !! 0,
        products !! 7 !! 1,
        products !! 6 !! 2,
        products !! 5 !! 3,
        products !! 4 !! 4,
        products !! 7 !! 5,
        products !! 3 !! 5,
        products !! 7 !! 6,
        products !! 6 !! 6,
        products !! 2 !! 6,
        products !! 6 !! 7,
        products !! 5 !! 7,
        products !! 1 !! 7
      ]
  -- out[1] = 2 # y[0] ⊕ 129 # y[1] ⊕ 192 # y[2] ⊕ 96 # y[3] ⊕ 48 # y[4] ⊕ 152 # y[5] ⊕ 76 # y[6] ⊕ 166 # y[7]
  --        = 0b00000010 # y[0] ⊕ 0b10000001 # y[1] ⊕ 0b11000000 # y[2] ⊕ 0b01100000 # y[3] ⊕ 0b00110000 # y[4] ⊕ 0b10011000 # y[5] ⊕ 0b01001100 # y[6] ⊕ 0b10100110 # y[7]
  --        = (x[1])y[0] ⊕ (x[7] + x[0])y[1] ⊕ (x[7] ⊕ x[6])y[2] ⊕ (x[6] ⊕ x[5])y[3] ⊕ (x[5] ⊕ x[4])y[4] ⊕ (x[7] ⊕ x[4] ⊕ x[3])y[5] ⊕ (x[6] ⊕ x[3] ⊕ x[2])y[6] ⊕ (x[7] ⊕ x[5] ⊕ x[2] ⊕ x[1])y[7]
  writeRefB (RefUBit out 1)
    =<< Boolean.xorBs
      [ products !! 1 !! 0,
        products !! 7 !! 1,
        products !! 0 !! 1,
        products !! 7 !! 2,
        products !! 6 !! 2,
        products !! 6 !! 3,
        products !! 5 !! 3,
        products !! 5 !! 4,
        products !! 4 !! 4,
        products !! 7 !! 5,
        products !! 4 !! 5,
        products !! 3 !! 5,
        products !! 6 !! 6,
        products !! 3 !! 6,
        products !! 2 !! 6,
        products !! 7 !! 7,
        products !! 5 !! 7,
        products !! 2 !! 7,
        products !! 1 !! 7
      ]
  -- out[2] = 4 # y[0] ⊕ 2 # y[1] ⊕ 129 # y[2] ⊕ 192 # y[3] ⊕ 96 # y[4] ⊕ 48 # y[5] ⊕ 152 # y[6] ⊕ 76 # y[7]
  --        = 0b00000100 # y[0] ⊕ 0b00000010 # y[1] ⊕ 0b10000001 # y[2] ⊕ 0b11000000 # y[3] ⊕ 0b01100000 # y[4] ⊕ 0b00110000 # y[5] ⊕ 0b10011000 # y[6] ⊕ 0b01001100 # y[7]
  --        = (x[2])y[0] ⊕ (x[1])y[1] ⊕ (x[7] ⊕ x[0])y[2] ⊕ (x[7] ⊕ x[6])y[3] ⊕ (x[6] ⊕ x[5])y[4] ⊕ (x[5] ⊕ x[4])y[5] ⊕ (x[7] ⊕ x[4] ⊕ x[3])y[6] ⊕ (x[6] ⊕ x[3] ⊕ x[2])y[7]
  writeRefB (RefUBit out 2)
    =<< Boolean.xorBs
      [ products !! 2 !! 0,
        products !! 1 !! 1,
        products !! 7 !! 2,
        products !! 0 !! 2,
        products !! 7 !! 3,
        products !! 6 !! 3,
        products !! 6 !! 4,
        products !! 5 !! 4,
        products !! 5 !! 5,
        products !! 4 !! 5,
        products !! 7 !! 6,
        products !! 4 !! 6,
        products !! 3 !! 6,
        products !! 6 !! 7,
        products !! 3 !! 7,
        products !! 2 !! 7
      ]
  -- out[3] = 8 # y[0] ⊕ 132 # y[1] ⊕ 66 # y[2] ⊕ 161 # y[3] ⊕ 208 # y[4] ⊕ 232 # y[5] ⊕ 244 # y[6] ⊕ 250 # y[7]
  --        = 0b00001000 # y[0] ⊕ 0b10000100 # y[1] ⊕ 0b01000010 # y[2] ⊕ 0b10100001 # y[3] ⊕ 0b11010000 # y[4] ⊕ 0b11101000 # y[5] ⊕ 0b11110100 # y[6] ⊕ 0b11111010 # y[7]
  --        = (x[3])y[0] ⊕ (x[7] ⊕ x[2])y[1] ⊕ (x[6] ⊕ x[1])y[2] ⊕ (x[7] ⊕ x[5] ⊕ x[0])y[3] ⊕ (x[7] ⊕ x[6] ⊕ x[4])y[4] ⊕ (x[7] ⊕ x[6] ⊕ x[5] ⊕ x[3])y[5] ⊕ (x[7] ⊕ x[6] ⊕ x[5] ⊕ x[4] ⊕ x[2])y[6] ⊕ (x[7] ⊕ x[6] ⊕ x[5] ⊕ x[4] ⊕ x[3] ⊕ x[1])y[7]
  writeRefB (RefUBit out 3)
    =<< Boolean.xorBs
      [ products !! 3 !! 0,
        products !! 7 !! 1,
        products !! 2 !! 1,
        products !! 6 !! 2,
        products !! 1 !! 2,
        products !! 7 !! 3,
        products !! 5 !! 3,
        products !! 0 !! 3,
        products !! 7 !! 4,
        products !! 6 !! 4,
        products !! 4 !! 4,
        products !! 7 !! 5,
        products !! 6 !! 5,
        products !! 5 !! 5,
        products !! 3 !! 5,
        products !! 7 !! 6,
        products !! 6 !! 6,
        products !! 5 !! 6,
        products !! 4 !! 6,
        products !! 2 !! 6,
        products !! 7 !! 7,
        products !! 6 !! 7,
        products !! 5 !! 7,
        products !! 4 !! 7,
        products !! 3 !! 7,
        products !! 1 !! 7
      ]
  -- out[4] = 16 # y[0] ⊕ 136 # y[1] ⊕ 196 # y[2] ⊕ 98 # y[3] ⊕ 177 # y[4] ⊕ 88 # y[5] ⊕ 44 # y[6] ⊕ 150 # y[7]
  --        = 0b00010000 # y[0] ⊕ 0b10001000 # y[1] ⊕ 0b11000100 # y[2] ⊕ 0b01100010 # y[3] ⊕ 0b10110001 # y[4] ⊕ 0b01011000 # y[5] ⊕ 0b00101100 # y[6] ⊕ 0b10010110 # y[7]
  --        = (x[4])y[0] ⊕ (x[7] ⊕ x[3])y[1] ⊕ (x[7] ⊕ x[6] ⊕ x[2])y[2] ⊕ (x[6] ⊕ x[5] ⊕ x[1])y[3] ⊕ (x[7] ⊕ x[5] ⊕ x[4] ⊕ x[0])y[4] ⊕ (x[6] ⊕ x[4] ⊕ x[3])y[5] ⊕ (x[5] ⊕ x[3] ⊕ x[2])y[6] ⊕ (x[7] ⊕ x[4] ⊕ x[2] ⊕ x[1])y[7]
  writeRefB (RefUBit out 4)
    =<< Boolean.xorBs
      [ products !! 4 !! 0,
        products !! 7 !! 1,
        products !! 3 !! 1,
        products !! 7 !! 2,
        products !! 6 !! 2,
        products !! 2 !! 2,
        products !! 6 !! 3,
        products !! 5 !! 3,
        products !! 1 !! 3,
        products !! 7 !! 4,
        products !! 5 !! 4,
        products !! 4 !! 4,
        products !! 0 !! 4,
        products !! 6 !! 5,
        products !! 4 !! 5,
        products !! 3 !! 5,
        products !! 5 !! 6,
        products !! 3 !! 6,
        products !! 2 !! 6,
        products !! 7 !! 7,
        products !! 4 !! 7,
        products !! 2 !! 7,
        products !! 1 !! 7
      ]
  -- out[5] = 32 # y[0] ⊕ 16 # y[1] ⊕ 136 # y[2] ⊕ 196 # y[3] ⊕ 98 # y[4] ⊕ 177 # y[5] ⊕ 88 # y[6] ⊕ 44 # y[7]
  --        = 0b00100000 # y[0] ⊕ 0b00010000 # y[1] ⊕ 0b10001000 # y[2] ⊕ 0b11000100 # y[3] ⊕ 0b01100010 # y[4] ⊕ 0b10110001 # y[5] ⊕ 0b01011000 # y[6] ⊕ 0b00101100 # y[7]
  --        = (x[5])y[0] ⊕ (x[4])y[1] ⊕ (x[7] ⊕ x[3])y[2] ⊕ (x[7] ⊕ x[6] ⊕ x[2])y[3] ⊕ (x[6] ⊕ x[5] ⊕ x[1])y[4] ⊕ (x[7] ⊕ x[5] ⊕ x[4] ⊕ x[0])y[5] ⊕ (x[6] ⊕ x[4] ⊕ x[3])y[6] ⊕ (x[5] ⊕ x[3] ⊕ x[2])y[7]
  writeRefB (RefUBit out 5)
    =<< Boolean.xorBs
      [ products !! 5 !! 0,
        products !! 4 !! 1,
        products !! 7 !! 2,
        products !! 3 !! 2,
        products !! 7 !! 3,
        products !! 6 !! 3,
        products !! 2 !! 3,
        products !! 6 !! 4,
        products !! 5 !! 4,
        products !! 1 !! 4,
        products !! 7 !! 5,
        products !! 5 !! 5,
        products !! 4 !! 5,
        products !! 0 !! 5,
        products !! 6 !! 6,
        products !! 4 !! 6,
        products !! 3 !! 6,
        products !! 5 !! 7,
        products !! 3 !! 7,
        products !! 2 !! 7
      ]
  -- out[6] = 64 # y[0] ⊕ 32 # y[1] ⊕ 16 # y[2] ⊕ 136 # y[3] ⊕ 196 # y[4] ⊕ 98 # y[5] ⊕ 177 # y[6] ⊕ 88 # y[7]
  --        = 0b01000000 # y[0] ⊕ 0b00100000 # y[1] ⊕ 0b00010000 # y[2] ⊕ 0b10001000 # y[3] ⊕ 0b11000100 # y[4] ⊕ 0b01100010 # y[5] ⊕ 0b10110001 # y[6] ⊕ 0b01011000 # y[7]
  --        = (x[6])y[0] ⊕ (x[5])y[1] ⊕ (x[4])y[2] ⊕ (x[7] ⊕ x[3])y[3] ⊕ (x[7] ⊕ x[6] ⊕ x[2])y[4] ⊕ (x[6] ⊕ x[5] ⊕ x[1])y[5] ⊕ (x[7] ⊕ x[5] ⊕ x[4] ⊕ x[0])y[6] ⊕ (x[6] ⊕ x[4] ⊕ x[3])y[7]
  writeRefB (RefUBit out 6)
    =<< Boolean.xorBs
      [ products !! 6 !! 0,
        products !! 5 !! 1,
        products !! 4 !! 2,
        products !! 7 !! 3,
        products !! 3 !! 3,
        products !! 7 !! 4,
        products !! 6 !! 4,
        products !! 2 !! 4,
        products !! 6 !! 5,
        products !! 5 !! 5,
        products !! 1 !! 5,
        products !! 7 !! 6,
        products !! 5 !! 6,
        products !! 4 !! 6,
        products !! 0 !! 6,
        products !! 6 !! 7,
        products !! 4 !! 7,
        products !! 3 !! 7
      ]

  -- out[7] = 128 # y[0] ⊕ 64 # y[1] ⊕ 32 # y[2] ⊕ 16 # y[3] ⊕ 136 # y[4] ⊕ 196 # y[5] ⊕ 98 # y[6] ⊕ 177 # y[7]
  --        = 0b10000000 # y[0] ⊕ 0b01000000 # y[1] ⊕ 0b00100000 # y[2] ⊕ 0b00010000 # y[3] ⊕ 0b10001000 # y[4] ⊕ 0b11000100 # y[5] ⊕ 0b01100010 # y[6] ⊕ 0b10110001 # y[7]
  --        = (x[7])y[0] ⊕ (x[6])y[1] ⊕ (x[5])y[2] ⊕ (x[4])y[3] ⊕ (x[7] ⊕ x[3])y[4] ⊕ (x[7] ⊕ x[6] ⊕ x[2])y[5] ⊕ (x[6] ⊕ x[5] ⊕ x[1])y[6] ⊕ (x[7] ⊕ x[5] ⊕ x[4] ⊕ x[0])y[7]
  writeRefB (RefUBit out 7)
    =<< Boolean.xorBs
      [ products !! 7 !! 0,
        products !! 6 !! 1,
        products !! 5 !! 2,
        products !! 4 !! 3,
        products !! 7 !! 4,
        products !! 3 !! 4,
        products !! 7 !! 5,
        products !! 6 !! 5,
        products !! 2 !! 5,
        products !! 6 !! 6,
        products !! 5 !! 6,
        products !! 1 !! 6,
        products !! 7 !! 7,
        products !! 5 !! 7,
        products !! 4 !! 7,
        products !! 0 !! 7
      ]
