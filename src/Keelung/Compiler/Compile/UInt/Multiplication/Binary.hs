module Keelung.Compiler.Compile.UInt.Multiplication.Binary (compileMulB) where

import Control.Monad
import Data.Field.Galois (GaloisField)
import Keelung (Width, widthOf)
import Keelung.Compiler.Compile.Monad
import Keelung.Data.Reference
import Keelung.Data.U (U)

compileMulB :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> Either RefU U -> M n ()
compileMulB _ _ _ (Right _) = error "[ panic ] compileMulB: not implemented"
compileMulB width out x (Left y) = do
  columns <- formHalfColumns width x y
  _carries <- foldColumns out columns
  return ()

-- wallace ::

-- | Form columns of bits to be added together after multiplication
--
--                                x₃      x₂      x₁      x₀
--   *)                           y₃      y₂      y₁      y₀
--   ----------------------------------------------------------
--                              x₃y₀    x₂y₀    x₁y₀    x₀y₀
--                      x₃y₁    x₂y₁    x₁y₁    x₀y₁
--              x₃y₂    x₂y₂    x₁y₂    x₀y₂
--      x₃y₃    x₂y₃    x₁y₃    x₀y₃
_formAllColumns :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> M n [(Int, [RefB])]
_formAllColumns width x y = do
  let numberOfColumns = 2 * width - 1
  let pairs = [(indexSum, [(RefUBit width x (indexSum - i), RefUBit width y i) | i <- [(indexSum - width + 1) `max` 0 .. indexSum `min` (width - 1)]]) | indexSum <- [0 .. numberOfColumns - 1]]
  forM pairs $ \(i, xs) -> do
    xs' <- mapM multiplyBits xs
    return (i, xs')

-- | Form only the right half of columns of bits to be added together after multiplication
--
--        x₃      x₂      x₁      x₀
--   *)   y₃      y₂      y₁      y₀
--   ---------------------------------
--      x₃y₀    x₂y₀    x₁y₀    x₀y₀
--      x₂y₁    x₁y₁    x₀y₁
--      x₁y₂    x₀y₂
--      x₀y₃
formHalfColumns :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> M n [(Int, [RefB])]
formHalfColumns width x y = do
  let numberOfColumns = width
  let pairs = [(indexSum, [(RefUBit width x (indexSum - i), RefUBit width y i) | i <- [0 `max` 0 .. indexSum]]) | indexSum <- [0 .. numberOfColumns - 1]]
  forM pairs $ \(i, xs) -> do
    xs' <- mapM multiplyBits xs
    return (i, xs')

-- | Starting from the least significant column, add the columns together and propagate the carry to the next column
foldColumns :: (GaloisField n, Integral n) => RefU -> [(Int, [RefB])] -> M n [RefB]
foldColumns out = foldM step []
  where
    step :: (GaloisField n, Integral n) => [RefB] -> (Int, [RefB]) -> M n [RefB]
    step prevCarries (columnIndex, column)
      | widthOf out <= columnIndex = return [] -- out of the range of `out`
      | otherwise = foldColumn (RefUBit (widthOf out) out columnIndex) (prevCarries <> column)

-- | Add up a column of bits and propagate the carry to the next column
foldColumn :: (GaloisField n, Integral n) => RefB -> [RefB] -> M n [RefB]
foldColumn _ [] = do
  return [] -- no carry
foldColumn out [a] = do
  combine1Bit out a
  return [] -- no carry
foldColumn out [a, b] = do
  carry <- combine2Bits out a b
  return [carry]
foldColumn out [a, b, c] = do
  carry <- combine3Bits out a b c
  return [carry]
foldColumn out (a : b : c : rest) = do
  tempOut <- freshRefB
  carry <- combine3Bits tempOut a b c
  carries <- foldColumn out (tempOut : rest)
  return $ carry : carries

combine1Bit :: (GaloisField n, Integral n) => RefB -> RefB -> M n ()
combine1Bit out a = addBits' out [a]

combine2Bits :: (GaloisField n, Integral n) => RefB -> RefB -> RefB -> M n RefB
combine2Bits out a b = do
  -- out[i] = a + b
  addBits' out [a, b]
  -- carry = a * b
  multiplyBits (a, b)

combine3Bits :: (GaloisField n, Integral n) => RefB -> RefB -> RefB -> RefB -> M n RefB
combine3Bits out a b c = do
  -- out[i] = a + b + c
  addBits' out [a, b, c]
  -- carry = a * b + a * c + b * c
  ab <- multiplyBits (a, b)
  ac <- multiplyBits (a, c)
  bc <- multiplyBits (b, c)
  addBits [ab, ac, bc]

-- | Add up a list of bits
addBits :: (GaloisField n, Integral n) => [RefB] -> M n RefB
addBits xs = do
  out <- freshRefB
  writeAdd 0 $ (B out, -1) : [(B x, 1) | x <- xs]
  return out

-- | Like `addBits` but write the result to an existing reference
addBits' :: (GaloisField n, Integral n) => RefB -> [RefB] -> M n ()
addBits' out xs = writeAdd 0 $ (B out, -1) : [(B x, 1) | x <- xs]

-- | Multiply two bits
multiplyBits :: (GaloisField n, Integral n) => (RefB, RefB) -> M n RefB
multiplyBits (x, y) = do
  out <- freshRefB
  multiplyBits' out (x, y)
  return out

-- | Like `multiplyBits` but write the result to an existing reference
multiplyBits' :: (GaloisField n, Integral n) => RefB -> (RefB, RefB) -> M n ()
multiplyBits' out (x, y) = writeMul (0, [(B x, 1)]) (0, [(B y, 1)]) (0, [(B out, 1)])
