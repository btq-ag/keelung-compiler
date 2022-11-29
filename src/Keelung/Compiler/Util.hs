module Keelung.Compiler.Util where

import Data.Field.Galois
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Keelung (N (N))
import Keelung.Syntax.Counters

-- A Witness is a mapping from variables to their values
type Witness n = IntMap n

showWitness :: (GaloisField n, Integral n) => Witness n -> String
showWitness xs =
  "["
    <> List.intercalate ", " (map (\(var, val) -> "$" <> show var <> " = " <> show (N val)) (IntMap.toList xs))
    <> "]"

showBooleanVars :: Counters -> String
showBooleanVars counters =
  let segments = getBooleanConstraintRanges counters
      showSegment (start, end) = 
          if start + 1 == end
          then "$" <> show start
          else "$" <> show start <> " .. $" <> show (end - 1)
      allSegments = List.intercalate ", " (map showSegment segments)
   in if getBooleanConstraintSize counters == 0
        then ""
        else "  Boolean constraints on: " <> allSegments <> "\n"
