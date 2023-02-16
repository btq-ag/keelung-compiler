{-# LANGUAGE DeriveFunctor #-}

module Keelung.Compiler.Syntax.Inputs where

import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Keelung.Compiler.Syntax.FieldBits (toBits)
import Keelung.Syntax.Counters
import Keelung.Syntax.Encode.Syntax (Computation (compCounters), Elaborated (elabComp))

-- | Deserialise the outputs from the R1CS interpreter
--   TODO: make it something like a proper inverse of Inputs.deserialize
removeBinRepsFromOutputs :: Counters -> [n] -> [n]
removeBinRepsFromOutputs counters outputs =
  let (start, end) = getOutputBinRepRange counters
   in take start outputs ++ drop end outputs

-- | Data structure for holding structured inputs
data Inputs n = Inputs
  { inputCounters :: Counters,
    inputPublic :: InputSequence n,
    inputPrivate :: InputSequence n
  }
  deriving (Eq, Show, Functor)

-- | Parse raw inputs into structured inputs and populate corresponding binary representations
deserialize :: (GaloisField n, Integral n) => Counters -> [n] -> [n] -> Inputs n
deserialize counters rawPublicInputs rawPrivateInputs = do
  -- go through all raw inputs
  -- sort and populate them with binary representation accordingly
  let publicInputSequence = new counters rawPublicInputs
      privateInputSequence = new counters rawPrivateInputs
   in Inputs counters publicInputSequence privateInputSequence

-- | Alternative version of 'deserialize' that accepts elaborated Keelung programs
deserializeElab :: (GaloisField n, Integral n) => Elaborated -> [n] -> [n] -> Inputs n
deserializeElab elab = deserialize (compCounters (elabComp elab))

-- | Concatenate all inputs into a single list
flatten :: (GaloisField n, Integral n) => Inputs n -> [n]
flatten (Inputs _ public private) = flattenInputSequence public <> flattenInputSequence private

-- | Size of all inputs
size :: (GaloisField n, Integral n) => Inputs n -> Int
size (Inputs counters _ _) =
  let (startPublic, _endPublic) = getPublicInputVarRange counters
      (_startPrivate, endPrivate) = getPrivateInputVarRange counters
   in endPrivate - startPublic

toIntMap :: (GaloisField n, Integral n) => Inputs n -> IntMap n
toIntMap (Inputs counters public private) =
  let (startPublic, endPublic) = getPublicInputVarRange counters
      (startPrivate, endPrivate) = getPrivateInputVarRange counters
   in IntMap.fromDistinctAscList (zip [startPublic .. endPublic - 1] (flattenInputSequence public))
        <> IntMap.fromDistinctAscList (zip [startPrivate .. endPrivate - 1] (flattenInputSequence private))

-- | Assuming that the variables are ordered as follows:
--      | output | public input | private input | intermediate
toVector :: (GaloisField n, Integral n) => Inputs n -> Vector (Maybe n)
toVector (Inputs counters public private) =
  let (startPublic, _endPublic) = getPublicInputVarRange counters
      (_startPrivate, endPrivate) = getPrivateInputVarRange counters
      totalCount = getTotalCount counters
   in Vector.replicate startPublic Nothing
        <> Vector.fromList (map Just (flattenInputSequence public))
        <> Vector.fromList (map Just (flattenInputSequence private))
        <> Vector.replicate (totalCount - endPrivate) Nothing

--------------------------------------------------------------------------------

data InputSequence n = InputSequence
  { seqField :: Seq n,
    seqBool :: Seq n,
    seqUInt :: IntMap (Seq n),
    seqUIntBinRep :: IntMap (Seq n)
  }
  deriving (Eq, Show, Functor)

instance Semigroup (InputSequence n) where
  InputSequence field1 bool1 uint1 uintBinRep1 <> InputSequence field2 bool2 uint2 uintBinRep2 =
    InputSequence
      (field1 <> field2)
      (bool1 <> bool2)
      (IntMap.unionWith (<>) uint1 uint2)
      (IntMap.unionWith (<>) uintBinRep1 uintBinRep2)

instance Monoid (InputSequence n) where
  mempty = InputSequence mempty mempty mempty mempty

new :: (GaloisField n, Integral n) => Counters -> [n] -> InputSequence n
new counters rawInputs =
  foldl
    ( \inputSequence ((inputType, _index), rawInputValue) ->
        case inputType of
          OfField -> addField rawInputValue inputSequence
          OfBoolean -> addBool rawInputValue inputSequence
          OfUIntBinRep _ -> error "[ panic ] OfUIntBinRep should not appear in the inputs sequence"
          OfUInt width -> addUInt width rawInputValue inputSequence
    )
    mempty
    (Seq.zip (getPublicInputSequence counters) (Seq.fromList rawInputs))

addField :: n -> InputSequence n -> InputSequence n
addField x (InputSequence field bool uint uintBinRep) = InputSequence (field Seq.:|> x) bool uint uintBinRep

addBool :: n -> InputSequence n -> InputSequence n
addBool x (InputSequence field bool uint uintBinRep) = InputSequence field (bool Seq.:|> x) uint uintBinRep

addUInt :: (GaloisField n, Integral n) => Int -> n -> InputSequence n -> InputSequence n
addUInt width x (InputSequence field bool uint uintBinRep) =
  InputSequence
    field
    bool
    (IntMap.insertWith (flip (<>)) width (Seq.singleton x) uint)
    (IntMap.insertWith (flip (<>)) width (Seq.fromList (take width (toBits x))) uintBinRep)

flattenInputSequence :: InputSequence n -> [n]
flattenInputSequence (InputSequence field bool uint uintBinRep) =
  toList field
    ++ toList bool
    ++ concatMap toList (IntMap.elems uintBinRep)
    ++ concatMap toList (IntMap.elems uint)
