module Keelung.Compiler.Compile.UInt.Multiplication.Binary (compileMulB, compileMulBExtended) where

import Control.Monad
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Keelung (Width, widthOf)
import Keelung.Compiler.Compile.Monad
import Keelung.Data.Reference
import Keelung.Data.U (U)

-- | Multiply two unsigned integers, get the result of the same width
compileMulB :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> Either RefU U -> M n ()
compileMulB width out x y = formHalfColumns width x y >>= foldColumns out

compileMulBExtended :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> Either RefU U -> M n ()
compileMulBExtended width out x y = formAllColumns width x y >>= foldColumns out

-- | Form columns of bits to be added together after multiplication
--
--                                x₃      x₂      x₁      x₀
--   *)                           y₃      y₂      y₁      y₀
--   ----------------------------------------------------------
--                              x₃y₀    x₂y₀    x₁y₀    x₀y₀
--                      x₃y₁    x₂y₁    x₁y₁    x₀y₁
--              x₃y₂    x₂y₂    x₁y₂    x₀y₂
--      x₃y₃    x₂y₃    x₁y₃    x₀y₃
formAllColumns :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU U -> M n [(Int, [RefB])]
formAllColumns width x (Left y) = do
  let numberOfColumns = 2 * width - 1
  let pairs = [(indexSum, [(RefUBit width x (indexSum - i), RefUBit width y i) | i <- [(indexSum - width + 1) `max` 0 .. indexSum `min` (width - 1)]]) | indexSum <- [0 .. numberOfColumns - 1]]
  forM pairs $ \(i, xs) -> do
    xs' <- mapM multiplyBits xs
    return (i, xs')
formAllColumns width x (Right y) = do
  let numberOfColumns = 2 * width - 1
  forM [0 .. numberOfColumns - 1] $ \i -> do
    -- put the bits of x into the column if `Data.Bits.testBit y j` is True
    let vars = [RefUBit width x (i - j) | j <- [(i - width + 1) `max` 0 .. i `min` (width - 1)], Data.Bits.testBit y j]
    return (i, vars)

-- | Form only the right half of columns of bits to be added together after multiplication
--
--        x₃      x₂      x₁      x₀
--   *)   y₃      y₂      y₁      y₀
--   ---------------------------------
--      x₃y₀    x₂y₀    x₁y₀    x₀y₀
--      x₂y₁    x₁y₁    x₀y₁
--      x₁y₂    x₀y₂
--      x₀y₃
formHalfColumns :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU U -> M n [(Int, [RefB])]
formHalfColumns width x (Left y) = do
  let numberOfColumns = width
  forM [0 .. numberOfColumns - 1] $ \i -> do
    let pairs = [(RefUBit width x (i - j), RefUBit width y j) | j <- [0 `max` 0 .. i]]
    xs' <- mapM multiplyBits pairs
    return (i, xs')
formHalfColumns width x (Right y) = do
  let numberOfColumns = width
  forM [0 .. numberOfColumns - 1] $ \i -> do
    -- put the bits of x into the column if `Data.Bits.testBit y j` is True
    let vars = [RefUBit width x (i - j) | j <- [0 `max` 0 .. i], Data.Bits.testBit y j]
    return (i, vars)

-- | Starting from the least significant column, add the bits together and propagate the carry to the next column
foldColumns :: (GaloisField n, Integral n) => RefU -> [(Int, [RefB])] -> M n ()
foldColumns out = foldM_ step []
  where
    step :: (GaloisField n, Integral n) => [RefB] -> (Int, [RefB]) -> M n [RefB]
    step prevCarries (columnIndex, column)
      | widthOf out <= columnIndex = return [] -- out of the range of `out`
      | otherwise = foldColumn (RefUBit (widthOf out) out columnIndex) (prevCarries <> column)

-- | Add up a column of bits and propagate the carry to the next column
foldColumn :: (GaloisField n, Integral n) => RefB -> [RefB] -> M n [RefB]
foldColumn out xs = do
  let (chunk, rest) = splitAt 3 xs
  if null rest
    then do
      -- last chunk
      combineBits out chunk
    else do
      -- handle the chunk
      tempOut <- freshRefB
      carry <- combineBits tempOut chunk
      -- push the result of the chunk back to the stack
      carries <- foldColumn out (tempOut : rest)
      return $ carry <> carries

-- | Add up a limited number of bits and return the carry
combineBits :: (GaloisField n, Integral n) => RefB -> [RefB] -> M n [RefB]
combineBits out [] = do
  writeRefVal (B out) 0
  return [] -- no carry
combineBits out [a] = do
  addBits' out [a]
  return [] -- no carry
combineBits out [a, b] = do
  -- out[i] = a + b
  addBits' out [a, b]
  -- carry = a * b
  carry <- multiplyBits (a, b)
  return [carry]
combineBits out [a, b, c] = do
  -- out[i] = a + b + c
  addBits' out [a, b, c]
  -- carry = a * b + a * c + b * c
  ab <- multiplyBits (a, b)
  ac <- multiplyBits (a, c)
  bc <- multiplyBits (b, c)
  carry <- addBits [ab, ac, bc]
  return [carry]
combineBits _ _ = error "[ panic ] combineBits: cannot handle too many bits"

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
