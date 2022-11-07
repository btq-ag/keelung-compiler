module Keelung.Compiler.Syntax.Inputs where

import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Keelung.Compiler.Syntax.Bits (toBits)
import Keelung.Syntax.Typed (Computation (compVarCounters), Elaborated (elabComp))
import Keelung.Syntax.VarCounters

-- | Data structure for holding structured inputs
data Inputs n = Inputs
  { varCounters :: VarCounters,
    numInputs :: Seq n,
    boolInputs :: Seq n,
    uintInputs :: IntMap (Seq n),
    numBinReps :: Seq n,
    uintBinReps :: IntMap (Seq n)
  }
  deriving (Eq, Show)

-- | Parse raw inputs into structured inputs and populate corresponding binary representations
deserialize :: (GaloisField n, Integral n) => VarCounters -> [n] -> Inputs n
deserialize counters rawInputs = do
  -- go through all raw inputs
  -- sort and populate them with binary representation accordingly

  -- let (numInputs', boolInputs', uintInputs', numBinReps', uintBinReps') =
  foldl
    ( \inputs (inputType, rawInput) ->
        case inputType of
          NumInput _ ->
            inputs
              { numInputs = numInputs inputs Seq.:|> rawInput,
                numBinReps = numBinReps inputs <> Seq.fromList (toBits rawInput)
              }
          BoolInput _ ->
            inputs
              { boolInputs = boolInputs inputs Seq.:|> rawInput
              }
          CustomInput width _ ->
            inputs
              { uintInputs = IntMap.insertWith (flip (<>)) width (Seq.singleton rawInput) (uintInputs inputs),
                uintBinReps = IntMap.insertWith (flip (<>)) width (Seq.fromList (toBits rawInput)) (uintBinReps inputs)
              }
    )
    (Inputs counters mempty mempty mempty mempty mempty)
    (Seq.zip (getInputSequence counters) (Seq.fromList rawInputs))

-- | Alternative version of 'deserialize' that accepts elaborated Keelung programs
deserializeElab :: (GaloisField n, Integral n) => Elaborated -> [n] -> Inputs n
deserializeElab elab = deserialize (compVarCounters (elabComp elab))

-- | Concatenate all inputs into a single list
flatten :: Inputs n -> [n]
flatten (Inputs _ a b c d e) =
  toList a
    <> toList b
    <> concatMap toList (IntMap.elems c)
    <> toList d
    <> concatMap toList (IntMap.elems e)

-- | Size of all inputs
size :: Inputs n -> Int
size = length . flatten

toIntMap :: Inputs n -> IntMap n
toIntMap inputs =
  let (start, _) = inputVarsRange (varCounters inputs)
   in IntMap.fromDistinctAscList (zip [start ..] (flatten inputs))