module Keelung.Compiler.Syntax.Inputs where

import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Sequence as Seq
import Keelung.Compiler.Syntax.Bits (toBits)
import Keelung.Syntax.Typed (Computation (compVarCounters), Elaborated (elabComp))
import Keelung.Syntax.VarCounters

-- | Data structure for holding structured inputs
data Inputs n = Inputs
  { varCounters :: VarCounters,
    numInputs :: [n],
    boolInputs :: [n],
    numBinReps :: [n]
  }
  deriving (Eq, Show)

-- | Parse raw inputs into structured inputs and populate corresponding binary representations
deserialize :: (GaloisField n, Integral n) => VarCounters -> [n] -> Inputs n
deserialize counters rawInputs = do
  -- go through all raw inputs
  -- sort and populate them with binary representation if it's a Number input
  let (numInputs', boolInputs', bitArrays) =
        foldl
          ( \(ns, bs, arrays) (inputType, rawInput) ->
              case inputType of
                NumInput key -> (IntMap.insert key rawInput ns, bs, arrays <> Seq.fromList (toBits rawInput))
                BoolInput key -> (ns, IntMap.insert key rawInput bs, arrays)
                CustomInput _width _key -> (ns, bs, arrays)
          )
          (mempty, mempty, mempty)
          (Seq.zip (getInputSequence counters) (Seq.fromList rawInputs))
   in Inputs
        { varCounters = counters,
          numInputs = IntMap.elems numInputs',
          boolInputs = IntMap.elems boolInputs',
          numBinReps = toList bitArrays
        }

-- | Alternative version of 'deserialize' that accepts elaborated Keelung programs
deserializeElab :: (GaloisField n, Integral n) => Elaborated -> [n] -> Inputs n
deserializeElab elab = deserialize (compVarCounters (elabComp elab))

-- | Concatenate all inputs into a single list
flatten :: Inputs n -> [n]
flatten (Inputs _ x y z) = x <> y <> z

-- | Size of all inputs
size :: Inputs n -> Int
size = length . flatten

toIntMap :: Inputs n -> IntMap n
toIntMap inputs =
  let (start, _) = inputVarsRange (varCounters inputs)
   in IntMap.fromDistinctAscList (zip [start ..] (flatten inputs))