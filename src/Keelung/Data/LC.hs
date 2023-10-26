module Keelung.Data.LC (LC (..), fromPolyL, toPolyL, fromRefU, fromRefU2, (@), neg, scale) where

import Data.Bits qualified
import Data.Field.Galois
import Keelung (FieldType (..), HasWidth (widthOf), Width)
import Keelung.Data.FieldInfo
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.U (U)

-- | Linear combination of variables and constants.
data LC n
  = Constant n
  | Polynomial (PolyL n)
  deriving (Eq, Show)

-- | Converting from 'Either n (PolyL n)'
fromPolyL :: Either n (PolyL n) -> LC n
fromPolyL = either Constant Polynomial

-- | Converting from a 'Either RefU U' to a list of 'LC n'.
fromRefU :: (Num n, Eq n, Show n, Ord n) => Width -> Either RefU U -> [LC n]
fromRefU fieldWidth (Right val) =
  map go [0, fieldWidth .. width - 1]
  where
    width = widthOf val
    go :: (Num n, Eq n) => Int -> LC n
    go limbStart = do
      let range = [0 .. (fieldWidth `min` width) - 1]
      Constant $ fromInteger $ sum [2 ^ i | i <- range, Data.Bits.testBit val (limbStart + i)]
fromRefU fieldWidth (Left var) =
  let limbs = Limb.refUToLimbs fieldWidth var
   in map (Polynomial . PolyL.fromLimb 0) limbs

-- | Converting from a 'Either RefU U' to a list of 'LC n'.
fromRefU2 :: (GaloisField n) => FieldInfo -> Either RefU U -> [LC n]
fromRefU2 fieldInfo (Right val) =
  let width = widthOf val
      go :: (Num n, Eq n) => Int -> LC n
      go limbStart = do
        let range = [0 .. (fieldWidth fieldInfo `min` width) - 1]
        Constant $ fromInteger $ sum [2 ^ i | i <- range, Data.Bits.testBit val (limbStart + i)]
   in case fieldTypeData fieldInfo of
        Binary _ -> [Constant (if Data.Bits.testBit val i then 1 else 0) | i <- [0 .. width - 1]]
        Prime _ -> map go [0, fieldWidth fieldInfo .. width - 1]
fromRefU2 fieldInfo (Left var) =
  let width = widthOf var
   in case fieldTypeData fieldInfo of
        Binary _ -> [1 @ B (RefUBit width var i) | i <- [0 .. width - 1]]
        Prime _ ->
          let limbs = Limb.refUToLimbs (fieldWidth fieldInfo) var
           in map (Polynomial . PolyL.fromLimb 0) limbs

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