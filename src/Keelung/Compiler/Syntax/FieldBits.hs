{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Like `Data.Bits` but with `Boolean` instead of `Bool`
module Keelung.Compiler.Syntax.FieldBits where

import Data.Bits qualified
import Data.Field.Galois
import Keelung

class (Integral a) => FieldBits a where
  {-# MINIMAL bitSize #-}
  bitSize :: a -> Int

  testBit' :: a -> Int -> Bool
  testBit' x i = Data.Bits.testBit (toInteger x) (i `mod` bitSize x)

  testBit :: a -> Int -> a
  testBit x i = if testBit' x i then 1 else 0

-- | All instances of Galois fields are also instances of `Bits`
--   `bitSize` will have to be calculated at runtime every time though,
--   It's recommended to declare specialized instances for each Galois fields
instance {-# OVERLAPPABLE #-} (GaloisField a, Integral a) => FieldBits a where
  bitSize x = go 0 (order x)
    where
      go i n = if n == 0 then i else go (i + 1) (Data.Bits.unsafeShiftR n 1)

-- | Specialized instance for `B64`
instance {-# INCOHERENT #-} FieldBits B64 where
  bitSize = const 64

-- | Specialized instance for `GF181`
instance {-# INCOHERENT #-} FieldBits GF181 where
  bitSize = const 181

-- | Specialized instance for `BN128`
instance {-# INCOHERENT #-} FieldBits BN128 where
  bitSize = const 254

--------------------------------------------------------------------------------

toBits :: (GaloisField a, Integral a) => a -> [a]
toBits x = map (testBit x) [0 .. bitSize x - 1]

toBits' :: (GaloisField a, Integral a) => Width -> Integer -> [a]
toBits' width x = map (\i -> if Data.Bits.testBit x i then 1 else 0) [0 .. width - 1]

fromBits :: Integral a => [a] -> Integer
fromBits = foldr (\x acc -> toInteger x + Data.Bits.shiftL acc 1) 0