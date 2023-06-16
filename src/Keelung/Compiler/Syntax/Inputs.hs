{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.Syntax.Inputs where

import Control.DeepSeq (NFData)
import Data.Foldable (Foldable (toList))
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Serialize (Serialize)
import Data.Vector (Vector)
import Data.Vector qualified as Vec
import GHC.Generics (Generic)
import Keelung
import Keelung.Compiler.Syntax.FieldBits qualified as FieldBits
import Keelung.Syntax.Counters

-- | Convert binary representation of inputs into human friendly Integers
--   TODO: make it something like a proper inverse of Inputs.deserialize
deserializeBinReps :: (GaloisField n, Integral n) => Counters -> Vector n -> Vector Integer
deserializeBinReps counters outputs =
  let sliceBits (width, count) =
        let offset = reindex counters Output (ReadUInt width) 0
         in [Vec.slice (offset + width * index) width outputs | index <- [0 .. count - 1]]
      binRepRanges = IntMap.toList (getUIntMap counters Output)
      bitArrays = concatMap sliceBits binRepRanges
      (start, _) = getRange counters (Output, ReadAllUInts)
      beforeBinReps = Vec.take start outputs
   in Vec.map toInteger beforeBinReps <> Vec.fromList (map (FieldBits.fromBits . toList) bitArrays)

-- | Data structure for holding structured inputs
data Inputs n = Inputs
  { inputCounters :: Counters,
    inputPublic :: InputSequence n,
    inputPrivate :: InputSequence n
  }
  deriving (Eq, Show, Functor)

-- | Parse raw inputs into structured inputs and populate corresponding binary representations
deserialize :: (GaloisField n, Integral n) => Counters -> [Integer] -> [Integer] -> Either Error (Inputs n)
deserialize counters rawPublicInputs rawPrivateInputs = do
  -- go through all raw inputs
  -- sort and populate them with binary representation accordingly
  let publicInputSequence = new (Seq.zip (getPublicInputSequence counters) (Seq.fromList rawPublicInputs))
      privateInputSequence = new (Seq.zip (getPrivateInputSequence counters) (Seq.fromList rawPrivateInputs))
      expectedPublicInputSize = length (getPublicInputSequence counters)
      expectedPrivateInputSize = length (getPrivateInputSequence counters)
      actualPublicInputSize = length rawPublicInputs
      actualPrivateInputSize = length rawPrivateInputs
   in if expectedPublicInputSize /= actualPublicInputSize
        then Left (PublicInputSizeMismatch expectedPublicInputSize actualPublicInputSize)
        else
          if expectedPrivateInputSize /= actualPrivateInputSize
            then Left (PrivateInputSizeMismatch expectedPrivateInputSize actualPrivateInputSize)
            else Right (Inputs counters publicInputSequence privateInputSequence)

-- | Size of all inputs
size :: (GaloisField n, Integral n) => Inputs n -> Int
size (Inputs counters _ _) = getCount counters PublicInput + getCount counters PrivateInput

toIntMap :: (GaloisField n, Integral n) => Inputs n -> IntMap n
toIntMap (Inputs counters public private) =
  let publicInputRanges = enumerate (getRanges counters [PublicInput])
      indexedPublicInput = IntMap.fromDistinctAscList $ zip publicInputRanges (toList (flattenInputSequence public))
      privateInputRanges = enumerate (getRanges counters [PrivateInput])
      indexedPrivateInput = IntMap.fromDistinctAscList $ zip privateInputRanges (toList (flattenInputSequence private))
   in indexedPublicInput <> indexedPrivateInput

--------------------------------------------------------------------------------

data InputSequence n = InputSequence
  { seqField :: Seq n,
    seqBool :: Seq n,
    seqUInt :: IntMap (Seq Integer),
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

new :: (GaloisField n, Integral n) => Seq (WriteType, Integer) -> InputSequence n
new =
  foldl
    ( \inputSequence (inputType, rawInputValue) ->
        case inputType of
          WriteField -> addField rawInputValue inputSequence
          WriteBool -> addBool rawInputValue inputSequence
          WriteUInt width -> addUInt width rawInputValue inputSequence
    )
    mempty

addField :: (GaloisField n, Integral n) => Integer -> InputSequence n -> InputSequence n
addField x (InputSequence field bool uint uintBinRep) = InputSequence (field Seq.:|> fromInteger x) bool uint uintBinRep

addBool :: (GaloisField n, Integral n) => Integer -> InputSequence n -> InputSequence n
addBool x (InputSequence field bool uint uintBinRep) = InputSequence field (bool Seq.:|> fromInteger x) uint uintBinRep

addUInt :: (GaloisField n, Integral n) => Int -> Integer -> InputSequence n -> InputSequence n
addUInt width x (InputSequence field bool uint uintBinRep) =
  InputSequence
    field
    bool
    (IntMap.insertWith (flip (<>)) width (Seq.singleton x) uint)
    (IntMap.insertWith (flip (<>)) width (Seq.fromList (take width (FieldBits.toBits' width x))) uintBinRep)

flattenInputSequence :: InputSequence n -> Seq n
flattenInputSequence (InputSequence field bool _uint uintBinRep) =
  field <> bool <> mconcat (IntMap.elems uintBinRep)

--------------------------------------------------------------------------------

data Error = PublicInputSizeMismatch Int Int | PrivateInputSizeMismatch Int Int
  deriving (Eq, Generic, NFData)

instance Show Error where
  show (PublicInputSizeMismatch expected actual) =
    "public input size mismatch: expected "
      ++ show expected
      ++ " but got "
      ++ show actual
  show (PrivateInputSizeMismatch expected actual) =
    "private input size mismatch: expected "
      ++ show expected
      ++ " but got "
      ++ show actual

instance Serialize Error
