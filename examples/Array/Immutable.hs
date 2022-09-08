{-# LANGUAGE DataKinds #-}

module Array.Immutable where

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

fullAdder :: Val ('Arr 'Bool) -> Val ('Arr 'Bool) -> Val ('Arr 'Bool)
fullAdder as bs =
  let zipped = zip (fromArray as) (fromArray bs)
   in toArray $ fst $ foldl f ([], false) zipped
  where
    f :: ([Val 'Bool], Val 'Bool) -> (Val 'Bool, Val 'Bool) -> ([Val 'Bool], Val 'Bool)
    f (acc, carry) (a, b) =
      let value = a `Xor` b `Xor` carry 
          nextCarry = (a `Xor` b `And` carry) `Or` (a `And` b)
       in (acc ++ [value], nextCarry)

-- | "T" for top-level
fullAdderT :: Int -> Comp (Val ('Arr 'Bool))
fullAdderT width = do
  xs <- inputs width
  ys <- inputs width
  return $ fullAdder xs ys

--------------------------------------------------------------------------------

multiplier :: Val ('Arr 'Bool) -> Int -> Val ('Arr 'Bool)
multiplier xs times = foldl fullAdder (toArray (replicate (lengthOf xs) false)) (replicate times xs)

-- | "T" for top-level
multiplierT :: Int -> Int -> Comp (Val ('Arr 'Bool))
multiplierT width times = do
  xs <- inputs width
  return $ multiplier xs times
