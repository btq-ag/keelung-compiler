{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Data.LC
  ( LC (..),
    new,
    (@),
    neg,
    (*.),
    fromRefU,
  )
where

import Control.DeepSeq (NFData)
import Data.Bits qualified
import Data.Field.Galois
import GHC.Generics (Generic)
import Keelung (HasWidth (widthOf))
import Keelung.Data.FieldInfo
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)

--------------------------------------------------------------------------------

-- | Linear combination of variables and constants.
data LC n
  = Constant n
  | Polynomial (PolyL n)
  deriving (Eq, Show, Generic, NFData)

-- | A LC is a semigroup under addition.
instance (Integral n, GaloisField n) => Semigroup (LC n) where
  Constant c <> Constant d = Constant (c + d)
  Polynomial xs <> Polynomial ys = fromEither (PolyL.merge xs ys)
  Polynomial xs <> Constant c = Polynomial (PolyL.addConstant c xs)
  Constant c <> Polynomial xs = Polynomial (PolyL.addConstant c xs)

-- | A LC is a monoid under addition.
instance (Integral n, GaloisField n) => Monoid (LC n) where
  mempty = Constant 0

-- | Construct a LC from a constant, Refs, and Limbs
new :: (Integral n, GaloisField n) => n -> [(Ref, n)] -> [(Slice, n)] -> LC n
new constant refs slices = fromEither (PolyL.new constant refs slices)

infixr 7 @

-- | Ref constructor
(@) :: (Integral n, GaloisField n) => n -> Ref -> LC n
n @ x = fromEither (PolyL.fromRefs 0 [(x, n)])

--------------------------------------------------------------------------------

-- | Converting from a 'Either RefU U' to a list of 'LC n'.
fromRefU :: (GaloisField n, Integral n) => FieldInfo -> Either RefU U -> [LC n]
fromRefU fieldInfo (Right val) =
  let width = widthOf val
      go :: (Num n, Eq n) => Int -> LC n
      go limbStart = do
        let range = [0 .. (fieldWidth fieldInfo `min` width) - 1]
        Constant $ fromInteger $ sum [2 ^ i | i <- range, Data.Bits.testBit val (limbStart + i)]
   in map go [0, fieldWidth fieldInfo .. width - 1]
fromRefU fieldInfo (Left var) =
  let slices = Slice.fromRefUWithDesiredWidth (fieldWidth fieldInfo) var
   in map (Polynomial . PolyL.fromSlice 0) slices

--------------------------------------------------------------------------------

infixl 7 ^*

-- | Scalar multiplication.
(^*) :: (Integral n, GaloisField n) => LC n -> n -> LC n
Constant c ^* n = Constant (n * c)
Polynomial xs ^* n = fromEither (PolyL.multiplyBy n xs)

infixr 7 *.

-- | Scalar multiplication.
(*.) :: (Integral n, GaloisField n) => n -> LC n -> LC n
(*.) = flip (^*)

-- | Negation.
neg :: (Integral n, GaloisField n) => LC n -> LC n
neg x = (-1) *. x

--------------------------------------------------------------------------------

-- | Helper function for converting from 'Either n (PolyL n)'
fromEither :: Either n (PolyL n) -> LC n
fromEither = either Constant Polynomial
