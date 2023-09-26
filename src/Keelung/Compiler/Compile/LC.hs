module Keelung.Compiler.Compile.LC (LC (..), fromPolyL, toPolyL, fromRefU, (@), neg, scale) where

import Data.Bits qualified
import Data.Field.Galois
import Keelung (Width)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference

-- | Linear combination of variables and constants.
data LC n
  = Constant n
  | Polynomial (PolyL n)
  deriving (Eq, Show)

-- | Converting from 'Either n (PolyL n)'
fromPolyL :: Either n (PolyL n) -> LC n
fromPolyL = either Constant Polynomial

-- | Converting from a 'Either RefU Integer' to a list of 'LC n'.
fromRefU :: (Num n, Eq n, Show n, Ord n) => Width -> Int -> Either RefU Integer -> [LC n]
fromRefU width fieldWidth (Right val) =
  let limbWidth = fieldWidth
   in map (go limbWidth) [0, limbWidth .. width - 1]
  where
    go :: (Num n, Eq n) => Int -> Int -> LC n
    go limbWidth limbStart = do
      let range = [limbStart .. (limbStart + limbWidth - 1) `min` (width - 1)]
      Constant $ fromInteger $ sum [2 ^ i | i <- range, Data.Bits.testBit val i]
fromRefU width fieldWidth (Left var) =
  let limbs = Limb.refUToLimbs (width `min` fieldWidth) var
   in map (\limb -> fromPolyL $ PolyL.fromLimbs 0 [(limb, 2 ^ Limb.lmbOffset limb)]) limbs

toPolyL :: (Num n, Eq n) => LC n -> Either n (PolyL n)
toPolyL (Constant c) = Left c
toPolyL (Polynomial xs) = Right xs

-- | A LC is a semigroup under addition.
instance (Semigroup n, GaloisField n) => Semigroup (LC n) where
  Constant c <> Constant d = Constant (c + d)
  Polynomial xs <> Polynomial ys = fromPolyL (PolyL.merge xs ys)
  Polynomial xs <> Constant c = Polynomial (PolyL.addConstant c xs)
  Constant c <> Polynomial xs = Polynomial (PolyL.addConstant c xs)

-- | A LC is a monoid under addition.
instance (Semigroup n, GaloisField n) => Monoid (LC n) where
  mempty = Constant 0

(@) :: GaloisField n => n -> Ref -> LC n
n @ x = fromPolyL (PolyL.fromRefs 0 [(x, n)])

neg :: GaloisField n => LC n -> LC n
neg = scale (-1)

scale :: GaloisField n => n -> LC n -> LC n
scale n (Constant c) = Constant (n * c)
scale n (Polynomial xs) = fromPolyL (PolyL.multiplyBy n xs)