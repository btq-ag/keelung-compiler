module Keelung.Compiler.Compile.UInt.Multiplication.Binary (compile) where

import Control.Monad
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Keelung (Width, widthOf)
import Keelung.Compiler.Compile.Monad
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice (Slice))
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U

-- | Multiply two unsigned integers, get the result of the same width
compile :: (GaloisField n, Integral n) => RefU -> RefU -> Either RefU U -> M n ()
compile out _ (Right 0) = writeRefUVal out 0
compile out refX operandY = do
  let outputWidth = widthOf out

  if outputWidth == widthOf refX
    then formHalfColumns outputWidth refX operandY >>= foldColumns out
    else -- range of product: 0 ... ((2 ^ widthOf sliceX) - 1) * valueY

      let productWidth = case operandY of
            Left refY -> widthOf refX + widthOf refY
            Right valueY -> U.widthOfInteger (((2 ^ widthOf refX) - 1) * toInteger valueY)
       in case outputWidth `compare` productWidth of
            LT -> do
              columns <- take outputWidth <$> formAllColumns productWidth refX operandY
              foldColumns out columns
            EQ -> do
              columns <- formAllColumns productWidth refX operandY
              foldColumns out columns
            GT -> do
              columns <- formAllColumns productWidth refX operandY
              foldColumns out columns
              -- the result is shorter than `out`
              -- write 0 to the higher bits of `out`
              let outSliceHI = Slice out productWidth outputWidth
              writeSliceVal outSliceHI 0

-- compileExtended :: (GaloisField n, Integral n) => RefU -> RefU -> Either RefU U -> M n ()
-- compileExtended out x y = formAllColumns x y >>= foldColumns out

-- | Form columns of bits to be added together after multiplication
--
--                                x₃      x₂      x₁      x₀
--   *)                           y₃      y₂      y₁      y₀
--   ----------------------------------------------------------
--                              x₃y₀    x₂y₀    x₁y₀    x₀y₀
--                      x₃y₁    x₂y₁    x₁y₁    x₀y₁
--              x₃y₂    x₂y₂    x₁y₂    x₀y₂
--      x₃y₃    x₂y₃    x₁y₃    x₀y₃
formAllColumns :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU U -> M n [(Int, [Bit])]
formAllColumns productWidth x (Left y) = do
  let width = widthOf x
  let pairs = [(indexSum, [((x, indexSum - i), (y, i)) | i <- [(indexSum - width + 1) `max` 0 .. indexSum `min` (width - 1)]]) | indexSum <- [0 .. productWidth - 1]]
  forM pairs $ \(i, xs) -> do
    xs' <- mapM multiplyBitsAlloc xs
    return (i, xs')
formAllColumns productWidth x (Right y) = do
  let width = widthOf x
  forM [0 .. productWidth - 1] $ \i -> do
    -- put the bits of x into the column if `Data.Bits.testBit y j` is True
    let vars = [(x, i - j) | j <- [(i - width + 1) `max` 0 .. i `min` (width - 1)], Data.Bits.testBit y j]
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
formHalfColumns :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU U -> M n [(Int, [Bit])]
formHalfColumns width x (Left y) = do
  let numberOfColumns = width
  forM [0 .. numberOfColumns - 1] $ \i -> do
    let pairs = [((x, i - j), (y, j)) | j <- [0 `max` 0 .. i]]
    xs' <- mapM multiplyBitsAlloc pairs
    return (i, xs')
formHalfColumns width x (Right y) = do
  let numberOfColumns = width
  forM [0 .. numberOfColumns - 1] $ \i -> do
    -- put the bits of x into the column if `Data.Bits.testBit y j` is True
    let vars = [(x, i - j) | j <- [0 `max` 0 .. i], Data.Bits.testBit y j]
    return (i, vars)

-- | Starting from the least significant column, add the bits together and propagate the carry to the next column
foldColumns :: (GaloisField n, Integral n) => RefU -> [(Int, [Bit])] -> M n ()
foldColumns out = foldM_ step []
  where
    step :: (GaloisField n, Integral n) => [Bit] -> (Int, [Bit]) -> M n [Bit]
    step prevCarries (columnIndex, column)
      | widthOf out <= columnIndex = return [] -- out of the range of `out`
      | otherwise = do
          let column' = prevCarries <> column
          foldColumn (out, columnIndex) column'

----------------------------------------

-- | Add up a column of bits and propagate the carry to the next column
foldColumn :: (GaloisField n, Integral n) => Bit -> [Bit] -> M n [Bit]
foldColumn out xs = do
  let (chunk, rest) = splitAt 3 xs
  if null rest
    then do
      -- last chunk
      combineBits out chunk
    else do
      -- handle the chunk
      tempOut <- do
        slice <- allocSlice 1
        return (Slice.sliceRefU slice, 0)
      carry <- combineBits tempOut chunk
      -- push the result of the chunk back to the stack
      carries <- foldColumn out (tempOut : rest)
      return $ carry <> carries

-- | Add up a limited number of bits and return the carry
combineBits :: (GaloisField n, Integral n) => Bit -> [Bit] -> M n [Bit]
combineBits (out, i) [] = do
  writeSliceVal (Slice out i (i + 1)) 0
  return [] -- no carry
combineBits out [a] = do
  addBits out [a]
  return [] -- no carry
combineBits out [a, b] = do
  -- bit allocation: 1
  -- out[i] = a + b
  addBits out [a, b]
  -- carry = a * b
  carry <- multiplyBitsAlloc (a, b)
  return [carry]
combineBits out [a, b, c] = do
  -- bit allocation: 4
  -- out[i] = a + b + c
  addBits out [a, b, c]
  -- carry = a * b + a * c + b * c
  ab <- multiplyBitsAlloc (a, b)
  ac <- multiplyBitsAlloc (a, c)
  bc <- multiplyBitsAlloc (b, c)
  carry <- addBitsAlloc [ab, ac, bc]
  return [carry]
combineBits _ _ = error "[ panic ] combineBits: cannot handle too many bits"

type Bit = (RefU, Int)

-- | Add up a list of bits
addBitsAlloc :: (GaloisField n, Integral n) => [Bit] -> M n Bit
addBitsAlloc xs = do
  out <- allocSlice 1
  writeAdd 0 [] ((out, -1) : [(Slice x i (i + 1), 1) | (x, i) <- xs])
  return (Slice.sliceRefU out, 0)

-- | Like `addBitsAlloc` but write the result to an existing reference
addBits :: (GaloisField n, Integral n) => Bit -> [Bit] -> M n ()
addBits (out, i) xs = writeAdd 0 [] ((Slice out i (i + 1), -1) : [(Slice x j (j + 1), 1) | (x, j) <- xs])

-- | Multiply two bits
multiplyBitsAlloc :: (GaloisField n, Integral n) => (Bit, Bit) -> M n Bit
multiplyBitsAlloc ((x, i), (y, j)) = do
  -- out <- freshRefB
  out <- allocSlice 1
  writeMul (0, [], [(Slice x i (i + 1), 1)]) (0, [], [(Slice y j (j + 1), 1)]) (0, [], [(out, 1)])
  return (Slice.sliceRefU out, 0)
