module Keelung.Compiler.Util where

import Data.Field.Galois
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.List qualified as List
import Keelung (N (N))

-- A Witness is a mapping from variables to their values
type Witness n = IntMap n

showWitness :: (GaloisField n, Integral n) => Witness n -> String
showWitness xs =
  "["
    <> List.intercalate ", " (map (\(var, val) -> "$" <> show var <> " = " <> show (N val)) (IntMap.toList xs))
    <> "]"

-- | Indent a string
indent :: String -> String
indent = unlines . map ("  " <>) . lines

-- | Show a list of strings
showList' :: [String] -> String
showList' xs = "[" <> List.intercalate ", " xs <> "]"

-- | Convert an integer to a string of subscripts
toSubscript :: Int -> String
toSubscript = map go . show
  where
    go c = case c of
      '0' -> '₀'
      '1' -> '₁'
      '2' -> '₂'
      '3' -> '₃'
      '4' -> '₄'
      '5' -> '₅'
      '6' -> '₆'
      '7' -> '₇'
      '8' -> '₈'
      '9' -> '₉'
      _ -> c
