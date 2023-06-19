module Keelung.Interpreter.Arithmetics where

import Data.Field.Galois (GaloisField)
import Keelung.Syntax (Width)
import Data.Bits (Bits(..))

--------------------------------------------------------------------------------

data U = UVal {uintWidth :: Width, uintValue :: Integer}
  deriving (Eq, Ord)

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

integerAddU :: U -> U -> U
integerAddU a b = UVal (uintWidth a) ((uintValue a + uintValue b) `mod` 2 ^ uintWidth a)

integerSubU :: U -> U -> U
integerSubU a b = UVal (uintWidth a) ((uintValue a - uintValue b) `mod` 2 ^ uintWidth a)

integerMulU :: U -> U -> U
integerMulU a b = UVal (uintWidth a) ((uintValue a * uintValue b) `mod` 2 ^ uintWidth a)

integerDivU :: U -> U -> U
integerDivU a b = UVal (uintWidth a) (uintValue a `div` uintValue b)

integerModU :: U -> U -> U
integerModU a b = UVal (uintWidth a) (uintValue a `mod` uintValue b)

bitWiseAndU :: U -> U -> U
bitWiseAndU a b = UVal (uintWidth a) (uintValue a .&. uintValue b)

bitWiseOrU :: U -> U -> U
bitWiseOrU a b = UVal (uintWidth a) (uintValue a .|. uintValue b)

bitWiseXorU :: U -> U -> U
bitWiseXorU a b = UVal (uintWidth a) (uintValue a `xor` uintValue b)

bitWiseNotU :: U -> U
bitWiseNotU a = UVal (uintWidth a) (complement (uintValue a))

-- | w is the bit width of the result
--   n is the amount to rotate left by
--   x is the value to be rotated
bitWiseRotateLU :: Width -> Int -> U -> U
bitWiseRotateLU w n a =
  UVal
    (uintWidth a)
    ( (uintValue a `Data.Bits.shiftL` fromIntegral (n `mod` w) Data.Bits..&. (2 ^ w - 1))
        Data.Bits..|. (uintValue a `Data.Bits.shiftR` fromIntegral (w - (n `mod` w)))
    )

-- | This function shifts left if n is positive and shifts right if n is negative
bitWiseShiftLU :: Width -> Int -> U -> U
bitWiseShiftLU w n a =
  UVal (uintWidth a) $
    if n < 0
      then Data.Bits.shiftR (uintValue a) (-n)
      else Data.Bits.shiftL (uintValue a) n Data.Bits..&. (2 ^ w - 1)

bitWiseSetU :: Width -> U -> Int -> Bool -> U
bitWiseSetU w x i b =
  let i' = i `mod` w
   in UVal (uintWidth x) $ if b
        then Data.Bits.clearBit (uintValue x) i'
        else Data.Bits.setBit (uintValue x) i'

--------------------------------------------------------------------------------

integerDiv :: (GaloisField n, Integral n) => n -> n -> n
integerDiv x y = fromInteger (toInteger x `div` toInteger y)

integerMod :: (GaloisField n, Integral n) => n -> n -> n
integerMod x y = fromInteger (toInteger x `mod` toInteger y)

bitWiseAnd :: (GaloisField n, Integral n) => n -> n -> n
bitWiseAnd x y = fromInteger $ (Data.Bits..&.) (toInteger x) (toInteger y)

bitWiseOr :: (GaloisField n, Integral n) => n -> n -> n
bitWiseOr x y = fromInteger $ (Data.Bits..|.) (toInteger x) (toInteger y)

bitWiseXor :: (GaloisField n, Integral n) => n -> n -> n
bitWiseXor x y = fromInteger $ Data.Bits.xor (toInteger x) (toInteger y)

bitWiseNot :: (GaloisField n, Integral n) => n -> n
bitWiseNot x = case toInteger x of
  0 -> 1
  _ -> 0

-- | w is the bit width of the result
--   n is the amount to rotate left by
--   x is the value to be rotated
bitWiseRotateL :: (GaloisField n, Integral n) => Width -> Int -> n -> n
bitWiseRotateL w n x =
  fromInteger $
    (toInteger x `Data.Bits.shiftL` fromIntegral (n `mod` w) Data.Bits..&. (2 ^ w - 1))
      Data.Bits..|. (toInteger x `Data.Bits.shiftR` fromIntegral (w - (n `mod` w)))

-- | This function shifts left if n is positive and shifts right if n is negative
bitWiseShiftL :: (GaloisField n, Integral n) => Width -> Int -> n -> n
bitWiseShiftL w n x =
  if n < 0
    then fromInteger $ Data.Bits.shiftR (toInteger x) (-n)
    else fromInteger $ Data.Bits.shiftL (toInteger x) n Data.Bits..&. (2 ^ w - 1)

bitWiseSet :: (GaloisField n, Integral n) => Width -> n -> Int -> Bool -> n
bitWiseSet w x i b =
  let i' = i `mod` w
   in if b
        then fromInteger $ Data.Bits.clearBit (toInteger x) i'
        else fromInteger $ Data.Bits.setBit (toInteger x) i'

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
