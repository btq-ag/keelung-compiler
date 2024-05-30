module Keelung.Compiler.Util where

import Data.Field.Galois
import Data.Field.Galois qualified as Field
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.List qualified as List
import Data.Proxy
import Debug.Trace qualified as Trace
import Keelung (GF181, N (N), gf181)
import Keelung.Data.FieldInfo (FieldInfo (..))

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

--------------------------------------------------------------------------------

-- | Default field info for GF181
gf181Info :: FieldInfo
gf181Info =
  let fieldNumber = asProxyTypeOf 0 (Proxy :: Proxy GF181)
   in FieldInfo
        { fieldTypeData = gf181,
          fieldOrder = toInteger (Field.order fieldNumber),
          fieldChar = Field.char fieldNumber,
          fieldDeg = fromIntegral (Field.deg fieldNumber),
          fieldWidth = floor (logBase (2 :: Double) (fromIntegral (Field.order fieldNumber)))
        }

--------------------------------------------------------------------------------

-- | Trace a message when a condition is met
traceWhen :: Bool -> String -> a -> a
traceWhen True msg = Trace.trace msg
traceWhen False _ = id

-- | Like 'traceWhen', but for monadic actions
traceWhenM :: (Monad m) => Bool -> String -> m ()
traceWhenM True msg = Trace.traceM msg
traceWhenM False _ = return ()

-- | Trace a message with a value when a condition is met
traceShowWhen :: (Show s) => Bool -> s -> a -> a
traceShowWhen True msg = Trace.traceShow msg
traceShowWhen False _ = id

-- | Like 'traceShowId', but only when a condition is met
traceShowIdWhen :: (Show s) => Bool -> s -> s
traceShowIdWhen True = Trace.traceShowId
traceShowIdWhen False = id

-- | Like 'traceShowWhen', but for monadic actions
traceShowWhenM :: (Monad m, Show s) => Bool -> s -> m ()
traceShowWhenM True msg = Trace.traceShowM msg
traceShowWhenM False _ = return ()

-- | Computes the powers of 2, takes care of negative powers and binary fields.
powerOf2 :: (Integral n, GaloisField n) => Int -> n
powerOf2 power =
  let two = 2
   in if two == 0
        then 1
        else
          if power < 0
            then recip (two ^ (-power))
            else two ^ power