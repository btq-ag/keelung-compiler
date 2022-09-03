{-# LANGUAGE DataKinds #-}

module Array.Mutable where

import Control.Monad (foldM_, foldM)
import Data.Bits (Bits (testBit))
import Data.Word (Word8)
import Keelung

fromWord8 :: Word8 -> Comp (Val ('ArrM 'Bool))
fromWord8 word = toArrayM $ Prelude.map (Boolean . testBit word) [0 .. 7]

fromChar :: Char -> Comp (Val ('ArrM 'Bool))
fromChar = fromWord8 . toEnum . fromEnum

fromString :: String -> Comp (Val ('ArrM ('ArrM 'Bool)))
fromString xs = toArrayM =<< mapM fromChar xs

fullAdder :: Val 'Bool -> Val 'Bool -> Val 'Bool -> (Val 'Bool, Val 'Bool)
fullAdder a b carry =
  let value = a `Xor` b `Xor` carry
      nextCarry = (a `Xor` b `And` carry) `Or` (a `And` b)
   in (value, nextCarry)

fullAdderN :: Int -> Val ('ArrM 'Bool) -> Val ('ArrM 'Bool) -> Comp (Val ('ArrM 'Bool))
fullAdderN width as bs = do
  -- allocate a new array of 64 bits for the result of the addition
  result <- toArrayM $ replicate width false
  -- 1-bit full adder
  foldM_
    ( \carry i -> do
        a <- accessM as i
        b <- accessM bs i
        let (value, nextCarry) = fullAdder a b carry
        updateM result i value
        return nextCarry
    )
    false
    [0 .. width - 1]
  return result

multiply :: Int -> Comp (Val ('ArrM 'Bool))
multiply times = do
  num <- inputs 32 >>= thaw
  z <- toArrayM $ replicate 32 false
  foldM (fullAdderN 32) z (replicate times num)
