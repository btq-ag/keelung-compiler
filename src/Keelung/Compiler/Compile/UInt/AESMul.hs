module Keelung.Compiler.Compile.UInt.AESMul (compileAESMulU) where

import Control.Monad.Except
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.Word (Word8)
import Keelung.Compiler.Compile.Boolean qualified as Boolean
import Keelung.Compiler.Compile.Monad
import Keelung.Data.Reference
import Keelung.Data.U qualified as U
import Keelung.Syntax (HasWidth (widthOf), Width)

--------------------------------------------------------------------------------

-- | GF(256) multiplication for AES
--   See https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf for more
compileAESMulU :: (GaloisField n, Integral n) => Int -> RefU -> Either RefU Integer -> Either RefU Integer -> M n ()
compileAESMulU width out (Right a) (Right b) = do
  let val = U.uValue (U.aesMul (U.new width a) (U.new width b))
  writeRefUVal out val
compileAESMulU width out (Right a) (Left b) = compileAESMulCV width out a b
compileAESMulU width out (Left a) (Right b) = compileAESMulCV width out b a
compileAESMulU width out (Left a) (Left b) = compileCLMul width out a b

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

-- | Derive the XorCode for a constant
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

-- | Generate a list of bits to be XORed from a Word8
codeToXors :: RefU -> Word8 -> [Either RefB Bool]
codeToXors ref code = [Left (RefUBit (widthOf ref) ref i) | i <- [0 .. 7], Data.Bits.testBit code i]

compileAESMulCV :: (GaloisField n, Integral n) => Width -> RefU -> Integer -> RefU -> M n ()
compileAESMulCV width out c x = do
  let (code0, code1, code2, code3, code4, code5, code6, code7) = calculateXorCode c
  Boolean.xorBs (codeToXors x code0) >>= writeRefB (RefUBit width out 0)
  Boolean.xorBs (codeToXors x code1) >>= writeRefB (RefUBit width out 1)
  Boolean.xorBs (codeToXors x code2) >>= writeRefB (RefUBit width out 2)
  Boolean.xorBs (codeToXors x code3) >>= writeRefB (RefUBit width out 3)
  Boolean.xorBs (codeToXors x code4) >>= writeRefB (RefUBit width out 4)
  Boolean.xorBs (codeToXors x code5) >>= writeRefB (RefUBit width out 5)
  Boolean.xorBs (codeToXors x code6) >>= writeRefB (RefUBit width out 6)
  Boolean.xorBs (codeToXors x code7) >>= writeRefB (RefUBit width out 7)

compileCLMul :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
compileCLMul width out x y = forM_ [0 .. width - 1] $ \i -> do
  -- pairs of bits to be conjuncted
  let pairs = [(RefUBit width x j, RefUBit width y (i - j)) | j <- [0 .. i]]
  -- conjunct the pairs
  conjunctedPairs <- sequence [Boolean.andBs [Left a, Left b] | (a, b) <- pairs]
  -- xor the conjuncted pairs
  result <- Boolean.xorBs conjunctedPairs
  case result of
    Left var -> writeRefBEq (RefUBit width out i) var
    Right val -> writeRefBVal (RefUBit width out i) val