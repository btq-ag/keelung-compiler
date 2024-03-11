{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Data.U
  ( U,
    new,
    widen,
    mapWidth,
    adjustWidth,
    slice,
    split,
    modInv,
    aesMul,
    clAdd,
    clMul,
    clDivMod,
    clDiv,
    clMod,
    chunks,
    widthOfInteger,
  )
where

import Control.DeepSeq (NFData)
import Data.Bits (Bits (..))
import Data.Bits qualified
import Data.Serialize (Serialize)
import Data.Word (Word32)
import GHC.Generics (Generic)
import Keelung.Syntax (HasWidth (..), Width)

--------------------------------------------------------------------------------

data U = U {uWidth :: Maybe Width, uValue :: Integer}
  deriving (Generic, NFData)

instance Eq U where
  a == b = uValue a == uValue b

instance Ord U where
  compare a b = compare (uValue a) (uValue b)

instance Serialize U

instance Show U where
  show (U _ value) = show value

instance HasWidth U where
  widthOf (U Nothing _) = 32 -- default width is 32
  widthOf (U (Just w) _) = w

instance Enum U where
  toEnum = fromIntegral
  fromEnum = fromIntegral

instance Num U where
  (+) = add
  (-) = sub
  (*) = mul
  abs = id
  signum = const 1
  fromInteger = U (Just 32)

instance Real U where
  toRational = toRational . uValue

instance Integral U where
  toInteger = uValue
  quotRem = divModU
  divMod = divModU

-- | Merging two U values by placing them side by side.
instance Semigroup U where
  (<>) a b = U (Just (widthOf a + widthOf b)) (uValue a `Data.Bits.shiftL` widthOf b Data.Bits..|. uValue b)

instance Monoid U where
  mempty = U (Just 0) 0

--------------------------------------------------------------------------------

new :: Width -> Integer -> U
new width value = U (Just width) (value `Prelude.mod` (2 ^ width))

widen :: Width -> U -> U
widen w (U Nothing value) = U (Just (w + 32)) value
widen w (U (Just v) value) = U (Just (w + v)) value

adjustWidth :: Width -> U -> U
adjustWidth width (U Nothing value) = U (Just width) (adjustWidthOfInteger 32 width value)
adjustWidth width (U (Just v) value) = U (Just width) (adjustWidthOfInteger v width value)

mapWidth :: (Width -> Width) -> U -> U
mapWidth _ (U Nothing value) = U Nothing value
mapWidth f (U (Just v) value) = U (Just (f v)) (adjustWidthOfInteger v (f v) value)

adjustWidthOfInteger :: Width -> Width -> Integer -> Integer
adjustWidthOfInteger oldWidth newWidth value = case oldWidth `compare` newWidth of
  EQ -> value -- no change
  LT -> value -- widen with zeros, no change
  GT -> value `Prelude.mod` (2 ^ newWidth) -- truncate

-- | Slice a U value into a smaller U value.
slice :: U -> (Int, Int) -> U
slice (U _ value) (start, end) = U (Just (end - start)) ((value `Data.Bits.shiftR` start) `Prelude.mod` (2 ^ (end - start)))

-- | Split a U value into two U values.
split :: U -> Int -> (U, U)
split u@(U _ value) index = 
  let width = widthOf u
      mask = (2 ^ index) - 1
      a = U (Just index) (value .&. mask)
      b = U (Just (width - index)) (value `Data.Bits.shiftR` index)
   in (a, b)

  
--------------------------------------------------------------------------------

add :: U -> U -> U
add a b =
  let width = mergeWidths a b
   in U (Just width) ((uValue a + uValue b) `Prelude.mod` 2 ^ width)

sub :: U -> U -> U
sub a b =
  let width = mergeWidths a b
   in U (Just width) ((uValue a - uValue b) `Prelude.mod` 2 ^ width)

mul :: U -> U -> U
mul a b =
  let width = mergeWidths a b
   in U (Just width) ((uValue a * uValue b) `Prelude.mod` 2 ^ width)

divModU :: U -> U -> (U, U)
divModU a b
  | uValue b == 0 = error "[ panic ] U.divMod: division by zero"
  | otherwise =
      let width = mergeWidths a b
       in (U (Just width) (uValue a `Prelude.div` uValue b), U (Just width) (uValue a `Prelude.mod` uValue b))

-- | Hardcoded GF(256) multiplication for AES
aesMul :: U -> U -> U
aesMul (U w a) (U _ b) =
  let a' = U (fmap (* 2) w) a
      b' = U (fmap (* 2) w) b
      U _ c' = snd $ (a' `clMul` b') `clDivMod` U (fmap (* 2) w) 0b100011011
   in U w c'

clAdd :: U -> U -> U
clAdd a b = U (Just width) (toInteger a `Data.Bits.xor` toInteger b)
  where
    width :: Width
    width = mergeWidths a b

-- | Carry-less multiplication of two unsigned integers.
clMul :: U -> U -> U
clMul a b = U (Just width) result
  where
    width :: Width
    width = mergeWidths a b

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
       in (U width quotient, U width remainder)
  where
    width :: Maybe Width
    width = Just (mergeWidths a b)

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

-- | Carry-less division of two unsigned integers.
clDiv :: U -> U -> U
clDiv a b = fst (clDivMod a b)

-- | Carry-less modulo of two unsigned integers.
clMod :: U -> U -> U
clMod a b = snd (clDivMod a b)

instance Bits U where
  (.&.) = bitWiseAndU
  (.|.) = bitWiseOrU
  xor = bitWiseXorU
  complement = bitWiseNotU
  shift = shiftU
  rotate = rotateU
  bitSizeMaybe = uWidth
  bitSize = widthOf
  isSigned = const False
  testBit a = testBit (uValue a)
  bit = U (Just 1) . bit
  popCount = popCount . uValue
  setBit = setBitU
  clearBit = clearBitU

bitWiseAndU :: U -> U -> U
bitWiseAndU a b = U (Just (mergeWidths a b)) (uValue a .&. uValue b)

bitWiseOrU :: U -> U -> U
bitWiseOrU a b = U (Just (mergeWidths a b)) (uValue a .|. uValue b)

bitWiseXorU :: U -> U -> U
bitWiseXorU a b = U (Just (mergeWidths a b)) (uValue a `xor` uValue b)

bitWiseNotU :: U -> U
bitWiseNotU a = U (uWidth a) (foldl complementBit (fromInteger (uValue a)) [0 .. widthOf a - 1])

-- | w is the bit width of the result
--   n is the amount to rotate left by
--   x is the value to be rotated
rotateU :: U -> Int -> U
rotateU a n =
  let w = widthOf a
   in U
        (uWidth a)
        ( (uValue a `Data.Bits.shiftL` fromIntegral (n `Prelude.mod` w) Data.Bits..&. (2 ^ w - 1))
            Data.Bits..|. (uValue a `Data.Bits.shiftR` fromIntegral (w - (n `Prelude.mod` w)))
        )

-- | This function shifts left if n is positive and shifts right if n is negative
--   Numbers gets smaller as you shift right
shiftU :: U -> Int -> U
shiftU a n =
  U (uWidth a) $
    if n < 0
      then Data.Bits.shiftR (uValue a) (-n)
      else Data.Bits.shiftL (uValue a) n Data.Bits..&. (2 ^ widthOf a - 1)

setBitU :: U -> Int -> U
setBitU x i =
  let i' = i `Prelude.mod` widthOf x
   in U (uWidth x) (Data.Bits.setBit (uValue x) i')

clearBitU :: U -> Int -> U
clearBitU x i =
  let i' = i `Prelude.mod` widthOf x
   in U (uWidth x) (Data.Bits.clearBit (uValue x) i')

-- | Split an integer into chunks of a specified size, the last chunk may be smaller.
chunks :: Int -> U -> [U]
chunks chunkSize (U Nothing num) = chunks chunkSize (U (Just 32) num)
chunks chunkSize (U (Just width) num)
  | width < 0 = error "[ panic ] U.chunks: Width must be non-negative"
  | width == 0 = []
  | width < chunkSize = [U (Just width) num]
  | otherwise = U (Just chunkSize) (num .&. mask) : chunks chunkSize (U (Just (width - chunkSize)) (num `shiftR` chunkSize))
  where
    mask = (2 ^ chunkSize) - 1

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

--------------------------------------------------------------------------------

-- | Helper function for joining two widths.
mergeWidths :: U -> U -> Width
mergeWidths (U Nothing _) (U Nothing _) = 32
mergeWidths (U (Just a) _) (U Nothing _) = a
mergeWidths (U Nothing _) (U (Just b) _) = b
mergeWidths (U (Just a) _) (U (Just b) _) = a `max` b

--------------------------------------------------------------------------------

-- | Calculate the number of bits required to represent an Integer.
widthOfInteger :: Integer -> Int
widthOfInteger 0 = 0
widthOfInteger x =
  let lowerBits = fromInteger x :: Word32
      higherBits = x `Data.Bits.shiftR` 32
   in if higherBits == 0
        then 32 - Data.Bits.countLeadingZeros lowerBits
        else 32 + widthOfInteger higherBits
