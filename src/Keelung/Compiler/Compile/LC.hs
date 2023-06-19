module Keelung.Compiler.Compile.LC (LC (..), fromEither, toEither, fromRefU, (@), neg, scale) where

import Data.Bits qualified
import Data.Field.Galois
import Keelung (Width)
import Keelung.Compiler.Constraint
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG

-- | Linear combination of variables and constants.
data LC n
  = Constant n
  | Polynomial (PolyG Ref n)
  deriving (Eq, Show)

-- | Converting from a 'Either n (PolyG Ref n)' to a 'LC n'.
fromEither :: Either n (PolyG Ref n) -> LC n
fromEither = either Constant Polynomial

-- | Converting from a 'Either RefU n' to a 'LC n'.
-- fromRefU :: (Num n, Eq n) => Width -> Either RefU Integer -> LC n
-- fromRefU _ (Right val) = Constant (fromInteger val)
-- fromRefU _ (Left var) =
--   let width = widthOf var
--       bits = [(B (RefUBit width var i), 2 ^ i) | i <- [0 .. width - 1]]
--    in fromEither (PolyG.build 0 bits)

fromRefU :: (Num n, Eq n) => Width -> Int -> Either RefU Integer -> [LC n]
fromRefU width fieldWidth (Right val) =
  let limbWidth = fieldWidth - 1
   in map (go limbWidth) [0, limbWidth .. width - 1]
  where
    go :: (Num n, Eq n) => Int -> Int -> LC n
    go limbWidth limbStart = do
      let range = [limbStart .. (limbStart + limbWidth - 1) `min` (width - 1)]
      Constant $ fromInteger $ sum [2 ^ i | i <- range, Data.Bits.testBit val i]
fromRefU width fieldWidth (Left var) =
  let limbWidth = fieldWidth - 1
   in map (go limbWidth) [0, limbWidth .. width - 1]
  where
    go :: (Num n, Eq n) => Int -> Int -> LC n
    go limbWidth limbStart = do
      let range = [limbStart .. (limbStart + limbWidth - 1) `min` (width - 1)]
      let bits = [(B (RefUBit width var i), 2 ^ i) | i <- range]
      fromEither (PolyG.build 0 bits)

-- let width = widthOf var
--     bits = [(B (RefUBit width var i), 2 ^ i) | i <- [0 .. width - 1]]
--  in fromEither (PolyG.build 0 bits)

toEither :: LC n -> Either n (PolyG Ref n)
toEither (Constant c) = Left c
toEither (Polynomial xs) = Right xs

-- | A LC is a semigroup under addition.
instance (Semigroup n, GaloisField n) => Semigroup (LC n) where
  Constant c <> Constant d = Constant (c + d)
  Polynomial xs <> Polynomial ys = fromEither (PolyG.merge xs ys)
  Polynomial xs <> Constant c = Polynomial (PolyG.addConstant c xs)
  Constant c <> Polynomial xs = Polynomial (PolyG.addConstant c xs)

-- | A LC is a monoid under addition.
instance (Semigroup n, GaloisField n) => Monoid (LC n) where
  mempty = Constant 0

-- var :: GaloisField n => Ref -> LC n
-- var x = fromEither (PolyG.singleton 0 (x, 1))

(@) :: GaloisField n => n -> Ref -> LC n
n @ x = fromEither (PolyG.singleton 0 (x, n))

neg :: GaloisField n => LC n -> LC n
neg = scale (-1)

scale :: GaloisField n => n -> LC n -> LC n
scale n (Constant c) = Constant (n * c)
scale n (Polynomial xs) = fromEither (PolyG.multiplyBy n xs)