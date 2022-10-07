{-# LANGUAGE DataKinds #-}

module Array.Immutable where

import Control.Monad
import Data.Bits (Bits (testBit))
import Data.Word (Word8)
import Keelung

fromWord8 :: Word8 -> Arr Boolean
fromWord8 word = toArray $ Prelude.map (Boolean . testBit word) [0 .. 7]

fromChar :: Char -> Arr Boolean
fromChar = fromWord8 . toEnum . fromEnum

fromString :: String -> Arr (Arr Boolean)
fromString = toArray . map fromChar

------------------------------------------------------------------------------

fullAdder :: Arr Boolean -> Arr Boolean -> Comp (Arr Boolean)
fullAdder as bs = do
  let zipped = zip (fromArray as) (fromArray bs)
  (result, _) <- foldM f ([], false) zipped
  return (toArray result)
  where
    f :: ([Boolean], Boolean) -> (Boolean, Boolean) -> Comp ([Boolean], Boolean)
    f (acc, carry) (a, b) = do
      xor <- reuse $ a `Xor` b
      carry' <- reuse carry
      let value = xor `Xor` carry'
      let nextCarry = (xor `And` carry') `Or` (a `And` b)
      return (acc ++ [value], nextCarry)

-- | "T" for top-level
fullAdderT :: Int -> Comp (Arr Boolean)
fullAdderT width = do
  xs <- inputs width
  ys <- inputs width
  fullAdder xs ys

--------------------------------------------------------------------------------

multiplier :: Arr Boolean -> Int -> Comp (Arr Boolean)
multiplier xs times =
  foldM
    fullAdder
    (toArray (replicate (length xs) false))
    (replicate times xs)

-- | "T" for top-level
multiplierT :: Int -> Int -> Comp (Arr Boolean)
multiplierT width times = do
  xs <- inputs width
  multiplier xs times
