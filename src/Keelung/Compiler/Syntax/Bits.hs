{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Like `Data.Bits` but with `Boolean` instead of `Bool`
module Keelung.Compiler.Syntax.Bits where

import qualified Data.Bits
import Data.Field.Galois
import Keelung

class (Integral a) => Bits a where
  {-# MINIMAL bitSize #-}
  bitSize :: a -> Int

  testBit :: a -> Int -> a
  testBit x i = if Data.Bits.testBit (toInteger x) (i `mod` bitSize x) then 1 else 0

-- | All instances of Galois fields are also instances of `Bits`
--   `bitSize` will have to be calculated at runtime every time though,
--   It's recommended to declare specialized instances for each Galois fields
instance {-# OVERLAPPABLE #-} (GaloisField a, Integral a) => Bits a where
  bitSize x = go 0 (order x)
    where
      go i n = if n == 0 then i else go (i + 1) (Data.Bits.unsafeShiftR n 1)

-- | Specialized instance for `B64`
instance {-# INCOHERENT #-} Bits B64 where
  bitSize = const 64

-- | Specialized instance for `GF181`
instance {-# INCOHERENT #-} Bits GF181 where
  bitSize = const 181

-- | Specialized instance for `BN128`
instance {-# INCOHERENT #-} Bits BN128 where
  bitSize = const 254