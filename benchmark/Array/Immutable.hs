{-# LANGUAGE DataKinds #-}
module Array.Immutable where

import Keelung 
import Data.Word (Word8)
import Data.Bits (Bits(testBit))

fromWord8 :: Word8 -> Val ('Arr 'Bool)
fromWord8 word = toArray $ Prelude.map (Boolean . testBit word) [0 .. 7]

fromChar :: Char -> Val ('Arr 'Bool)
fromChar = fromWord8 . toEnum . fromEnum

fromString :: String -> Val ('Arr ('Arr 'Bool)) 
fromString = toArray . map fromChar


fullAdder :: Val 'Bool -> Val 'Bool -> Val 'Bool -> (Val 'Bool, Val 'Bool)
fullAdder a b carry = (value, nextCarry)
  where
    value = a `Xor` b `Xor` carry
    nextCarry = (a `Xor` b `And` carry) `Or` (a `And` b)

fullAdderN :: Val ('Arr 'Bool) -> Val ('Arr 'Bool) -> Val ('Arr 'Bool)
fullAdderN as bs =
  let zipped = zip (fromArray as) (fromArray bs)
   in toArray $ fst $ foldl f ([], false) zipped
  where
    f :: ([Val 'Bool], Val 'Bool) -> (Val 'Bool, Val 'Bool) -> ([Val 'Bool], Val 'Bool)
    f (acc, carry) (a, b) =
      let (value', carry') = fullAdder a b carry
       in (acc ++ [value'], carry')

multiply :: Int -> Comp (Val ('Arr 'Bool))
multiply times = do
  num <- inputs 32
  let z = toArray $ replicate 32 false 
  return $ foldl fullAdderN z (replicate times num)

  