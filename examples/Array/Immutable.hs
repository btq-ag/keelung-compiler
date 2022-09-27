{-# LANGUAGE DataKinds #-}

module Array.Immutable where

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

fullAdder :: Arr Boolean -> Arr Boolean -> Arr Boolean
fullAdder as bs =
  let zipped = zip (fromArray as) (fromArray bs)
   in toArray $ fst $ foldl f ([], false) zipped
  where
    f :: ([Boolean], Boolean) -> (Boolean, Boolean) -> ([Boolean], Boolean)
    f (acc, carry) (a, b) =
      let value = a `Xor` b `Xor` carry 
          nextCarry = (a `Xor` b `And` carry) `Or` (a `And` b)
       in (acc ++ [value], nextCarry)

-- | "T" for top-level
fullAdderT :: Int -> Comp (Arr Boolean)
fullAdderT width = do
  xs <- inputs width
  ys <- inputs width
  return $ fullAdder xs ys

--------------------------------------------------------------------------------

multiplier :: Arr Boolean -> Int -> Arr Boolean
multiplier xs times = foldl fullAdder (toArray (replicate (length xs) false)) (replicate times xs)

-- | "T" for top-level
multiplierT :: Int -> Int -> Comp (Arr Boolean)
multiplierT width times = do
  xs <- inputs width
  return $ multiplier xs times
