module Keelung.Interpreter.Arithmetics where

import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Keelung.Syntax (Width)

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

-- w is the bit width of the result
-- n is the amount to shift left by
-- x is the value to shift
bitWiseRotateL :: (GaloisField n, Integral n) => Width -> Int -> n -> n
bitWiseRotateL w n x =
  fromInteger $
    (toInteger x `Data.Bits.shiftL` fromIntegral (n `mod` w) Data.Bits..&. (2 ^ w - 1))
      Data.Bits..|. (toInteger x `Data.Bits.shiftR` fromIntegral (w - (n `mod` w)))

bitWiseShiftL :: (GaloisField n, Integral n) => Width -> Int -> n -> n
bitWiseShiftL w n x =
  if n < 0
    then fromInteger $ Data.Bits.shiftR (toInteger x) (-n)
    else fromInteger $ Data.Bits.shiftL (toInteger x) n Data.Bits..&. (2 ^ w - 1)

bitWiseSet :: (GaloisField n, Integral n) => Width -> n -> Int -> n -> n
bitWiseSet w x i b =
  let i' = i `mod` w
   in case toInteger b of
        0 -> fromInteger $ Data.Bits.clearBit (toInteger x) i'
        _ -> fromInteger $ Data.Bits.setBit (toInteger x) i'

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
