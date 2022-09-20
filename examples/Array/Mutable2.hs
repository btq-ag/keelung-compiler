{-# LANGUAGE DataKinds #-}

module Array.Mutable2 where

import Control.Monad 
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

alloc :: Comp (Val ('ArrM 'Bool))
alloc = toArrayM [false]

set :: Val ('ArrM 'Bool) -> Val 'Bool -> Comp ()
set ref = updateM ref 0

get :: Val ('ArrM 'Bool) -> Comp (Val 'Bool)
get ref = accessM ref 0

fullAdder :: Val ('ArrM 'Bool) -> Val ('ArrM 'Bool) -> Comp (Val ('ArrM 'Bool))
fullAdder as bs = do
  xor <- alloc
  carryRef <- alloc
  -- allocate a new array of 64 bits for the result of the addition
  result <- toArrayM $ replicate (lengthOfM as) false
  -- 1-bit full adder
  forM_ [0 .. lengthOfM as - 1] $ \i -> do
    a <- accessM as i
    b <- accessM bs i
    set xor (a `Xor` b)
    x <- get xor
    carry <- get carryRef
    let value = x `Xor` carry
    set carryRef $ (x `And` carry) `Or` (a `And` b)
    updateM result i value
    return ()

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

multiplierT :: Int -> Int -> Comp (Val ('ArrM 'Bool))
multiplierT width times = do
  xs <- inputs width >>= thaw
  multiplier xs times
