module Keelung.Compiler.Compile.LC (LC (..), fromPolyG, toPolyL, fromRefU, (@), neg, scale) where

import Data.Bits qualified
import Data.Field.Galois
import Keelung (Width)
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference

-- | Linear combination of variables and constants.
data LC n
  = Constant n
  | Polynomial (PolyG n)
  deriving (Eq, Show)

-- | Converting from a 'Either n (PolyG n)' to a 'LC n'.
fromPolyG :: Either n (PolyG n) -> LC n
fromPolyG = either Constant Polynomial

-- | Converting from a 'Either RefU Integer' to a list of 'LC n'.
fromRefU :: (Num n, Eq n) => Width -> Int -> Either RefU Integer -> [LC n]
fromRefU width fieldWidth (Right val) =
  let limbWidth = fieldWidth
   in map (go limbWidth) [0, limbWidth .. width - 1]
  where
    go :: (Num n, Eq n) => Int -> Int -> LC n
    go limbWidth limbStart = do
      let range = [limbStart .. (limbStart + limbWidth - 1) `min` (width - 1)]
      Constant $ fromInteger $ sum [2 ^ i | i <- range, Data.Bits.testBit val i]
fromRefU width fieldWidth (Left var) =
  let limbWidth = fieldWidth
   in map (go limbWidth) [0, limbWidth .. width - 1]
  where
    go :: (Num n, Eq n) => Int -> Int -> LC n
    go limbWidth limbStart = do
      let range = [limbStart .. (limbStart + limbWidth - 1) `min` (width - 1)]
      let bits = [(B (RefUBit width var i), 2 ^ i) | i <- range]
      fromPolyG (PolyG.build 0 bits)

toPolyL :: (Num n, Eq n) => LC n -> Either n (PolyL n)
toPolyL (Constant c) = Left c
toPolyL (Polynomial xs) = Right (PolyL.fromPolyG xs)

-- | A LC is a semigroup under addition.
instance (Semigroup n, GaloisField n) => Semigroup (LC n) where
  Constant c <> Constant d = Constant (c + d)
  Polynomial xs <> Polynomial ys = fromPolyG (PolyG.merge xs ys)
  Polynomial xs <> Constant c = Polynomial (PolyG.addConstant c xs)
  Constant c <> Polynomial xs = Polynomial (PolyG.addConstant c xs)

-- | A LC is a monoid under addition.
instance (Semigroup n, GaloisField n) => Monoid (LC n) where
  mempty = Constant 0

-- var :: GaloisField n => Ref -> LC n
-- var x = fromPolyG (PolyG.singleton 0 (x, 1))

(@) :: GaloisField n => n -> Ref -> LC n
n @ x = fromPolyG (PolyG.singleton 0 (x, n))

neg :: GaloisField n => LC n -> LC n
neg = scale (-1)

scale :: GaloisField n => n -> LC n -> LC n
scale n (Constant c) = Constant (n * c)
scale n (Polynomial xs) = fromPolyG (PolyG.multiplyBy n xs)