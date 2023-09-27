{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Data.U
  ( U (uWidth, uValue),
    new,
    add,
    sub,
    mul,
    div,
    mod,
    modInv,
    clMul,
    clDivMod,
    chunks,
  )
where

import Control.DeepSeq (NFData)
import Data.Bits (Bits (..))
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.Util
import Keelung.Syntax (Width)
import Prelude hiding (div, mod)
import Prelude qualified

--------------------------------------------------------------------------------

data U = UVal {uWidth :: Width, uValue :: Integer}
  deriving (Eq, Ord, Generic, NFData)

instance Serialize U

instance Show U where
  show (UVal _ value) = show value

instance Enum U where
  toEnum = error "[ panic ] toEnum not implemented for U"
  fromEnum = error "[ panic ] fromEnum not implemented for U"

-- instance Num U where
--   a + b = UVal (uWidth a) ((uValue a + uValue b) `mod` 2 ^ uWidth a)
--   a - b = UVal (uWidth a) ((uValue a - uValue b) `mod` 2 ^ uWidth a)
--   a * b = UVal (uWidth a) ((uValue a * uValue b) `mod` 2 ^ uWidth a)
--   abs = id
--   signum = const 1
--   fromInteger _ = error "[ panic ] fromInteger not implemented for U"

-- instance Real U where
--   toRational = toRational . uValue

-- instance Integral U where
--   toInteger = uValue
--   quotRem a b = (UVal (uWidth a) (uValue a `quot` uValue b), UVal (uWidth a) (uValue a `rem` uValue b))

--------------------------------------------------------------------------------

new :: Width -> Integer -> U
new width value = UVal width (value `Prelude.mod` (2 ^ width))

--------------------------------------------------------------------------------

add :: U -> U -> U
add a b = UVal (uWidth a) ((uValue a + uValue b) `Prelude.mod` 2 ^ uWidth a)

sub :: U -> U -> U
sub a b = UVal (uWidth a) ((uValue a - uValue b) `Prelude.mod` 2 ^ uWidth a)

mul :: U -> U -> U
mul a b = UVal (uWidth a) ((uValue a * uValue b) `Prelude.mod` 2 ^ uWidth a)

div :: U -> U -> U
div a b =
  if uValue b == 0
    then error "[ panic ] U.div: division by zero in "
    else UVal (uWidth a) (uValue a `Prelude.div` uValue b)

mod :: U -> U -> U
mod a b = UVal (uWidth a) (uValue a `Prelude.mod` uValue b)

-- | Carry-less multiplication of two unsigned integers.
clMul :: U -> U -> U
clMul a b = UVal width result
  where
    width :: Width
    width = uWidth a

    -- calculate the bits
    bits :: Int -> Bool
    bits index = foldl Data.Bits.xor False [Data.Bits.testBit (uValue a) i Data.Bits..&. Data.Bits.testBit (uValue b) (index - i) | i <- [0 .. index]]

    -- assemble the bits
    result :: Integer
    result = foldl (\acc i -> if bits i then Data.Bits.setBit acc i else acc) 0 [0 .. width - 1]

-- | Carry-less DivMod of two unsigned integers.
clDivMod :: U -> U -> (U, U)
clDivMod a b
  | uValue b == 0 = error "[ panic ] U.clDivMod: division by zero"
  | otherwise =
      let (quotient, remainder) = longDivision (uValue a) (uValue b)
       in (UVal width quotient, UVal width remainder)
  where
    width :: Width
    width = uWidth a

    -- schoolbook long division
    longDivision :: Integer -> Integer -> (Integer, Integer)
    longDivision dividend divisor =
      let dividendWidth = widthOfInteger dividend
          divisorWidth = widthOfInteger divisor
       in if divisorWidth > dividendWidth
            then (0, dividend)
            else
              let power = dividendWidth - divisorWidth
                  (quotient, remainder) = longDivision (dividend `Data.Bits.xor` (divisor `Data.Bits.shiftL` power)) divisor
               in (quotient `Data.Bits.setBit` power, remainder)

instance Bits U where
  (.&.) = bitWiseAndU
  (.|.) = bitWiseOrU
  xor = bitWiseXorU
  complement = bitWiseNotU
  shift = shiftU
  rotate = rotateU
  bitSizeMaybe = Just . uWidth
  bitSize = uWidth
  isSigned = const False
  testBit a = testBit (uValue a)
  bit = UVal 1 . bit
  popCount = popCount . uValue
  setBit = setBitU
  clearBit = clearBitU

bitWiseAndU :: U -> U -> U
bitWiseAndU a b = UVal (uWidth a) (uValue a .&. uValue b)

bitWiseOrU :: U -> U -> U
bitWiseOrU a b = UVal (uWidth a) (uValue a .|. uValue b)

bitWiseXorU :: U -> U -> U
bitWiseXorU a b = UVal (uWidth a) (uValue a `xor` uValue b)

bitWiseNotU :: U -> U
bitWiseNotU a = UVal (uWidth a) (foldl complementBit (fromInteger (uValue a)) [0 .. uWidth a - 1])

-- | w is the bit width of the result
--   n is the amount to rotate left by
--   x is the value to be rotated
rotateU :: U -> Int -> U
rotateU a n =
  let w = uWidth a
   in UVal
        (uWidth a)
        ( (uValue a `Data.Bits.shiftL` fromIntegral (n `Prelude.mod` w) Data.Bits..&. (2 ^ w - 1))
            Data.Bits..|. (uValue a `Data.Bits.shiftR` fromIntegral (w - (n `Prelude.mod` w)))
        )

-- | This function shifts left if n is positive and shifts right if n is negative
--   Numbers gets smaller as you shift right
shiftU :: U -> Int -> U
shiftU a n =
  UVal (uWidth a) $
    if n < 0
      then Data.Bits.shiftR (uValue a) (-n)
      else Data.Bits.shiftL (uValue a) n Data.Bits..&. (2 ^ uWidth a - 1)

setBitU :: U -> Int -> U
setBitU x i =
  let i' = i `Prelude.mod` uWidth x
   in UVal (uWidth x) (Data.Bits.setBit (uValue x) i')

clearBitU :: U -> Int -> U
clearBitU x i =
  let i' = i `Prelude.mod` uWidth x
   in UVal (uWidth x) (Data.Bits.clearBit (uValue x) i')

-- | Split an integer into chunks of a specified size, the last chunk may be smaller.
chunks :: Int -> U -> [U]
chunks chunkSize (UVal width num)
  | width < 0 = error "[ panic ] U.chunks: Width must be non-negative"
  | width == 0 = []
  | width < chunkSize = [UVal width num]
  | otherwise = UVal chunkSize (num .&. mask) : chunks chunkSize (UVal (width - chunkSize) (num `shiftR` chunkSize))
  where
    mask = (2 ^ chunkSize) - 1

-- splitU :: Int -> U -> [U]
-- splitU size (UVal w x) = map (UVal size) (splitInteger x size w)
--   where
--     -- Split an integer into chunks of a specified size and return both the split chunks
--     -- and the last partial chunk (if it exists).
--     splitInteger :: Integer -> Int -> Int -> ([Integer], Maybe (Integer, Int))
--     splitInteger n chunkSize totalBits
--         | totalBits <= 0 || chunkSize <= 0 = ([], Nothing)
--         | otherwise =
--             let (chunks, lastChunk) = split n chunkSize totalBits []
--             in case lastChunk of
--                 0 -> (chunks, Nothing)  -- The last chunk is full-sized.
--                 _ -> (chunks, Just (last (n `Data.Bits.shiftR` (totalBits - lastChunk)), lastChunk))

--     -- Split the integer into chunks and calculate the size of the last chunk.
--     split :: Integer -> Int -> Int -> [Integer] -> ([Integer], Int)
--     split n chunkSize totalBits chunks
--         | totalBits <= 0 = (reverse chunks, 0)
--         | otherwise =
--             let mask = (1 `shiftL` chunkSize) - 1
--                 chunk = n Data.Bits..&. mask
--                 (remainingChunks, lastChunkSize) = split (n `Data.Bits.shiftR` chunkSize) chunkSize (totalBits - chunkSize) (chunk : chunks)
--             in (remainingChunks, chunkSize + lastChunkSize)

--------------------------------------------------------------------------------

-- Given m and a, return Just x such that ax = 1 mod m.
-- If there is no such x return Nothing.
modInv :: Integer -> Integer -> Maybe Integer
modInv x p =
  let (i, _, g) = gcdExt x p
   in if g == 1 then Just (makePositive i) else Nothing
  where
    makePositive y = if y < 0 then y + p else y
    -- Extended Euclidean algorithm.  Given non-negative a and b, return x, y and g
    -- such that ax + by = g, where g = gcd(a,b).  Note that x or y may be negative.
    gcdExt a 0 = (1, 0, a)
    gcdExt a b =
      let (q, r) = a `quotRem` b
          (s, t, g) = gcdExt b r
       in (t, s - q * t, g)
