module Keelung.Data.LC
  ( LC (..),
    fromPolyL,
    toPolyL,
    fromRefU,
    (@),
    neg,
    scale,
  )
where

import Data.Bits qualified
import Data.Field.Galois
import Keelung (HasWidth (widthOf))
import Keelung.Data.FieldInfo
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.U (U)
-- import qualified Keelung.Data.Slice as Slice

-- | Linear combination of variables and constants.
data LC n
  = Constant n
  | Polynomial (PolyL n)
  deriving (Eq, Show)

-- | Converting from 'Either n (PolyL n)'
fromPolyL :: Either n (PolyL n) -> LC n
fromPolyL = either Constant Polynomial

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
  -- case PolyL.new 0 [] [(Slice.fromRefU var, 1)] of 
  -- Left constant -> [Constant constant]
  -- Right poly -> [Polynomial poly]
  let limbs = Limb.refUToLimbs (fieldWidth fieldInfo) var
   in map (Polynomial . PolyL.fromLimb 0) limbs

toPolyL :: (Num n, Eq n) => LC n -> Either n (PolyL n)
toPolyL (Constant c) = Left c
toPolyL (Polynomial xs) = Right xs

-- | A LC is a semigroup under addition.
instance (Integral n, GaloisField n) => Semigroup (LC n) where
  Constant c <> Constant d = Constant (c + d)
  Polynomial xs <> Polynomial ys = fromPolyL (PolyL.merge xs ys)
  Polynomial xs <> Constant c = Polynomial (PolyL.addConstant c xs)
  Constant c <> Polynomial xs = Polynomial (PolyL.addConstant c xs)

-- | A LC is a monoid under addition.
instance (Integral n, GaloisField n) => Monoid (LC n) where
  mempty = Constant 0

(@) :: (Integral n, GaloisField n) => n -> Ref -> LC n
n @ x = fromPolyL (PolyL.fromRefs 0 [(x, n)])

neg :: (Integral n, GaloisField n) => LC n -> LC n
neg = scale (-1)

scale :: (Integral n, GaloisField n) => n -> LC n -> LC n
scale n (Constant c) = Constant (n * c)
scale n (Polynomial xs) = fromPolyL (PolyL.multiplyBy n xs)