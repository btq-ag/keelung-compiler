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

indent :: String -> String
indent = unlines . map ("  " <>) . lines