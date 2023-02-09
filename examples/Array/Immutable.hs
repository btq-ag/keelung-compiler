{-# LANGUAGE DataKinds #-}

module Array.Immutable where

import Control.Monad
import Data.Bits (Bits (testBit))
import Data.Word (Word8)
import Keelung

fromWord8 :: Word8 -> [Boolean]
fromWord8 word = Prelude.map (Boolean . testBit word) [0 .. 7]

fromChar :: Char -> [Boolean]
fromChar = fromWord8 . toEnum . fromEnum

fromString :: String -> [[Boolean]]
fromString = map fromChar

------------------------------------------------------------------------------

fullAdder :: [Boolean] -> [Boolean] -> Comp [Boolean]
fullAdder as bs = do
  let zipped = zip as bs
  (result, _) <- foldM f ([], false) zipped
  return result
  where
    f :: ([Boolean], Boolean) -> (Boolean, Boolean) -> Comp ([Boolean], Boolean)
    f (acc, carry) (a, b) = do
      xor <- reuse $ a `Xor` b
      carry' <- reuse carry
      let value = xor `Xor` carry'
      let nextCarry = (xor `And` carry') `Or` (a `And` b)
      return (acc ++ [value], nextCarry)

-- | "T" for top-level
fullAdderT :: Int -> Comp [Boolean]
fullAdderT width = do
  xs <- inputList width
  ys <- inputList width
  fullAdder xs ys

--------------------------------------------------------------------------------

multiplier :: [Boolean] -> Int -> Comp [Boolean]
multiplier xs times =
  foldM
    fullAdder
    (replicate (length xs) false)
    (replicate times xs)

-- | "T" for top-level
multiplierT :: Int -> Int -> Comp [Boolean]
multiplierT width times = do
  xs <- inputList width
  multiplier xs times
