{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Interpreter.Arithmetics
  ( U (uintWidth, uintValue),
    new,
    chunksU,
    integerAddU,
    integerSubU,
    integerMulU,
    integerDivU,
    integerModU,
    modInv,
  )
where

import Control.DeepSeq (NFData)
import Data.Bits (Bits (..))
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung.Syntax (Width)

--------------------------------------------------------------------------------

data U = UVal {uintWidth :: Width, uintValue :: Integer}
  deriving (Eq, Ord, Generic, NFData)

instance Serialize U

instance Show U where
  show (UVal _ value) = show value

instance Enum U where
  toEnum = error "[ panic ] toEnum not implemented for U"
  fromEnum = error "[ panic ] fromEnum not implemented for U"

-- instance Num U where
--   a + b = UVal (uintWidth a) ((uintValue a + uintValue b) `mod` 2 ^ uintWidth a)
--   a - b = UVal (uintWidth a) ((uintValue a - uintValue b) `mod` 2 ^ uintWidth a)
--   a * b = UVal (uintWidth a) ((uintValue a * uintValue b) `mod` 2 ^ uintWidth a)
--   abs = id
--   signum = const 1
--   fromInteger _ = error "[ panic ] fromInteger not implemented for U"

-- instance Real U where
--   toRational = toRational . uintValue

-- instance Integral U where
--   toInteger = uintValue
--   quotRem a b = (UVal (uintWidth a) (uintValue a `quot` uintValue b), UVal (uintWidth a) (uintValue a `rem` uintValue b))

--------------------------------------------------------------------------------

new :: Width -> Integer -> U
new width value = UVal width (value `mod` (2 ^ width))

--------------------------------------------------------------------------------

integerAddU :: U -> U -> U
integerAddU a b = UVal (uintWidth a) ((uintValue a + uintValue b) `mod` 2 ^ uintWidth a)

integerSubU :: U -> U -> U
integerSubU a b = UVal (uintWidth a) ((uintValue a - uintValue b) `mod` 2 ^ uintWidth a)

integerMulU :: U -> U -> U
integerMulU a b = UVal (uintWidth a) ((uintValue a * uintValue b) `mod` 2 ^ uintWidth a)

integerDivU :: U -> U -> U
integerDivU a b =
  if uintValue b == 0
    then error "[ panic ] division by zero in U.integerDivU"
    else UVal (uintWidth a) (uintValue a `div` uintValue b)

integerModU :: U -> U -> U
integerModU a b = UVal (uintWidth a) (uintValue a `mod` uintValue b)

instance Bits U where
  (.&.) = bitWiseAndU
  (.|.) = bitWiseOrU
  xor = bitWiseXorU
  complement = bitWiseNotU
  shift = shiftU
  rotate = rotateU
  bitSizeMaybe = Just . uintWidth
  bitSize = uintWidth
  isSigned = const False
  testBit a = testBit (uintValue a)
  bit = UVal 1 . bit
  popCount = popCount . uintValue
  setBit = setBitU
  clearBit = clearBitU

bitWiseAndU :: U -> U -> U
bitWiseAndU a b = UVal (uintWidth a) (uintValue a .&. uintValue b)

bitWiseOrU :: U -> U -> U
bitWiseOrU a b = UVal (uintWidth a) (uintValue a .|. uintValue b)

bitWiseXorU :: U -> U -> U
bitWiseXorU a b = UVal (uintWidth a) (uintValue a `xor` uintValue b)

bitWiseNotU :: U -> U
bitWiseNotU a = UVal (uintWidth a) (foldl complementBit (fromInteger (uintValue a)) [0 .. uintWidth a - 1])

-- | w is the bit width of the result
--   n is the amount to rotate left by
--   x is the value to be rotated
rotateU :: U -> Int -> U
rotateU a n =
  let w = uintWidth a
   in UVal
        (uintWidth a)
        ( (uintValue a `Data.Bits.shiftL` fromIntegral (n `mod` w) Data.Bits..&. (2 ^ w - 1))
            Data.Bits..|. (uintValue a `Data.Bits.shiftR` fromIntegral (w - (n `mod` w)))
        )

-- | This function shifts left if n is positive and shifts right if n is negative
--   Numbers gets smaller as you shift right
shiftU :: U -> Int -> U
shiftU a n =
  UVal (uintWidth a) $
    if n < 0
      then Data.Bits.shiftR (uintValue a) (-n)
      else Data.Bits.shiftL (uintValue a) n Data.Bits..&. (2 ^ uintWidth a - 1)

setBitU :: U -> Int -> U
setBitU x i =
  let i' = i `mod` uintWidth x
   in UVal (uintWidth x) (Data.Bits.setBit (uintValue x) i')

clearBitU :: U -> Int -> U
clearBitU x i =
  let i' = i `mod` uintWidth x
   in UVal (uintWidth x) (Data.Bits.clearBit (uintValue x) i')

-- | Split an integer into chunks of a specified size, the last chunk may be smaller.
chunksU :: Int -> U -> [U]
chunksU chunkSize (UVal width num)
  | width < 0 = error "[ panic ] U.chunks: Width must be non-negative"
  | width == 0 = []
  | width < chunkSize = [UVal width num]
  | otherwise = UVal chunkSize (num .&. mask) : chunksU chunkSize (UVal (width - chunkSize) (num `shiftR` chunkSize))
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
