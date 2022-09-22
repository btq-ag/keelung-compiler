{-# LANGUAGE DataKinds #-}

module Array.Immutable2 where

import Control.Monad
import Data.Bits (Bits (testBit))
import Data.Word (Word8)
import Keelung

fromWord8 :: Word8 -> Val ('Arr 'Bool)
fromWord8 word = toArray $ Prelude.map (Boolean . testBit word) [0 .. 7]

fromChar :: Char -> Val ('Arr 'Bool)
fromChar = fromWord8 . toEnum . fromEnum

fromString :: String -> Val ('Arr ('Arr 'Bool))
fromString = toArray . map fromChar

------------------------------------------------------------------------------

fullAdder :: Val ('Arr 'Bool) -> Val ('Arr 'Bool) -> Comp (Val ('Arr 'Bool))
fullAdder as bs = do 
  let zipped = zip (fromArray as) (fromArray bs)
  (result, _) <- foldM f ([], false) zipped
  return (toArray result)
  where
    f :: ([Val 'Bool], Val 'Bool) -> (Val 'Bool, Val 'Bool) -> Comp ([Val 'Bool], Val 'Bool)
    f (acc, carry) (a, b) = do
      xor <- reuse $ a `Xor` b
      carry' <- reuse carry
      let value = xor `Xor` carry'
      let nextCarry = (xor `And` carry') `Or` (a `And` b)
      return (acc ++ [value], nextCarry)

-- | "T" for top-level
fullAdderT :: Int -> Comp (Val ('Arr 'Bool))
fullAdderT width = do
  xs <- inputs width
  ys <- inputs width
  fullAdder xs ys

--------------------------------------------------------------------------------

multiplier :: Val ('Arr 'Bool) -> Int -> Comp (Val ('Arr 'Bool))
multiplier xs times = 
  foldM 
    fullAdder 
    (toArray (replicate (lengthOf xs) false)) 
    (replicate times xs)

-- | "T" for top-level
multiplierT :: Int -> Int -> Comp (Val ('Arr 'Bool))
multiplierT width times = do
  xs <- inputs width
  multiplier xs times
