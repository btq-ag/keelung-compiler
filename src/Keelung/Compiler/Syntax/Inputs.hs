{-# LANGUAGE DeriveFunctor #-}

module Keelung.Compiler.Syntax.Inputs where

import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Keelung.Compiler.Syntax.FieldBits (toBits)
import Keelung.Syntax.Counters
import Keelung.Syntax.Typed (Computation (compCounters), Elaborated (elabComp))

-- | Deserialise the outputs from the R1CS interpreter
--   TODO: make it something like a proper inverse of Inputs.deserialize
removeBinRepsFromOutputs :: Counters -> [n] -> [n]
removeBinRepsFromOutputs counters outputs =
  let (start, end) = getOutputBinRepRange counters
   in take start outputs ++ drop end outputs

-- | Data structure for holding structured inputs
data Inputs n = Inputs
  { varCounters :: Counters,
    numInputs :: Seq n,
    boolInputs :: Seq n,
    uintInputs :: IntMap (Seq n),
    -- numBinReps :: Seq n,
    uintBinReps :: IntMap (Seq n)
  }
  deriving (Eq, Show, Functor)

-- | Parse raw inputs into structured inputs and populate corresponding binary representations
deserialize :: (GaloisField n, Integral n) => Counters -> [n] -> Inputs n
deserialize counters rawInputs = do
  -- go through all raw inputs
  -- sort and populate them with binary representation accordingly

  -- let (numInputs', boolInputs', uintInputs', numBinReps', uintBinReps') =
  foldl
    ( \inputs ((inputType, _index), rawInputValue) ->
        case inputType of
          OfField ->
            inputs
              { numInputs = numInputs inputs Seq.:|> rawInputValue
              -- numBinReps = numBinReps inputs <> Seq.fromList (toBits rawInputValue)
              }
          OfBoolean ->
            inputs
              { boolInputs = boolInputs inputs Seq.:|> rawInputValue
              }
          OfUIntBinRep _ -> error "[ panic ] OfUIntBinRep should not appear in the inputs sequence"
          OfUInt width ->
            inputs
              { uintInputs = IntMap.insertWith (flip (<>)) width (Seq.singleton rawInputValue) (uintInputs inputs),
                uintBinReps = IntMap.insertWith (flip (<>)) width (Seq.fromList (take width (toBits rawInputValue))) (uintBinReps inputs)
              }
    )
    (Inputs counters mempty mempty mempty mempty)
    (Seq.zip (getInputSequence counters) (Seq.fromList rawInputs))

-- | Alternative version of 'deserialize' that accepts elaborated Keelung programs
deserializeElab :: (GaloisField n, Integral n) => Elaborated -> [n] -> Inputs n
deserializeElab elab = deserialize (compCounters (elabComp elab))

-- | Concatenate all inputs into a single list
flatten :: Inputs n -> [n]
flatten (Inputs _ f b u ubr) =
  toList f
    <> toList b
    <> concatMap toList (IntMap.elems ubr)
    <> concatMap toList (IntMap.elems u)

-- | Size of all inputs
size :: Inputs n -> Int
size = length . flatten

toIntMap :: Inputs n -> IntMap n
toIntMap inputs =
  let (start, _) = getInputVarRange (varCounters inputs)
   in IntMap.fromDistinctAscList (zip [start ..] (flatten inputs))

toVector :: Inputs n -> Vector (Maybe n)
toVector inputs =
  let (start, end) = getInputVarRange (varCounters inputs)
      totalCount = getTotalCount (varCounters inputs)
   in Vector.replicate start Nothing
        <> Vector.fromList (map Just (flatten inputs))
        <> Vector.replicate (totalCount - end) Nothing
