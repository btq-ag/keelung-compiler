{-# LANGUAGE DataKinds #-}

module Array.Mutable where

import Control.Monad (foldM, foldM_)
import Data.Bits (Bits (testBit))
import Data.Word (Word8)
import Keelung

fromWord8 :: Word8 -> Comp (ArrM Boolean)
fromWord8 word = toArrayM $ Prelude.map (Boolean . testBit word) [0 .. 7]

fromChar :: Char -> Comp (ArrM Boolean)
fromChar = fromWord8 . toEnum . fromEnum

fromString :: String -> Comp (ArrM (ArrM Boolean))
fromString xs = toArrayM =<< mapM fromChar xs

------------------------------------------------------------------------------

fullAdder :: ArrM Boolean -> ArrM Boolean -> Comp (ArrM Boolean)
fullAdder as bs = do
  -- allocate a new array of 64 bits for the result of the addition
  result <- toArrayM $ replicate (lengthOf as) false
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
    [0 .. lengthOf as - 1]
  return result

-- | "T" for top-level
fullAdderT :: Int -> Comp (ArrM Boolean)
fullAdderT width = do
  xs <- inputs width >>= thaw
  ys <- inputs width >>= thaw
  fullAdder xs ys

--------------------------------------------------------------------------------

multiplier :: ArrM Boolean -> Int -> Comp (ArrM Boolean)
multiplier xs times = foldM fullAdder xs (replicate times xs)

multiplierT :: Int -> Int -> Comp (ArrM Boolean)
multiplierT width times = do
  xs <- inputs width >>= thaw
  multiplier xs times
