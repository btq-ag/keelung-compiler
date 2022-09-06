{-# LANGUAGE DataKinds #-}

module Array.Mutable where

import Control.Monad (foldM, foldM_)
import Data.Bits (Bits (testBit))
import Data.Word (Word8)
import Keelung

fromWord8 :: Word8 -> Comp (Val ('ArrM 'Bool))
fromWord8 word = toArrayM $ Prelude.map (Boolean . testBit word) [0 .. 7]

fromChar :: Char -> Comp (Val ('ArrM 'Bool))
fromChar = fromWord8 . toEnum . fromEnum

fromString :: String -> Comp (Val ('ArrM ('ArrM 'Bool)))
fromString xs = toArrayM =<< mapM fromChar xs

------------------------------------------------------------------------------

fullAdder :: Val ('ArrM 'Bool) -> Val ('ArrM 'Bool) -> Comp (Val ('ArrM 'Bool))
fullAdder as bs = do
  -- allocate a new array of 64 bits for the result of the addition
  result <- toArrayM $ replicate (lengthOfM as) false
  -- 1-bit full adder
  foldM_
    ( \carry i -> do
        a <- accessM as i
        b <- accessM bs i
        let value = a `Xor` b `Xor` carry
        let nextCarry = (a `Xor` b `And` carry) `Or` (a `And` b)
        updateM result i value
        return nextCarry
    )
    false
    [0 .. lengthOfM as - 1]
  return result

-- | "T" for top-level
fullAdderT :: Int -> Comp (Val ('ArrM 'Bool))
fullAdderT width = do
  xs <- inputs width >>= thaw
  ys <- inputs width >>= thaw
  fullAdder xs ys

--------------------------------------------------------------------------------

multiplier :: Val ('ArrM 'Bool) -> Int -> Comp (Val ('ArrM 'Bool))
multiplier xs times = foldM fullAdder xs (replicate times xs)

multiplyT :: Int -> Int -> Comp (Val ('ArrM 'Bool))
multiplyT width times = do
  xs <- inputs width >>= thaw
  multiplier xs times
