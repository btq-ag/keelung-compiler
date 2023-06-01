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
import GHC.Generics (Generic)
import Keelung
import Keelung.Compiler.Syntax.FieldBits (toBits)
import Keelung.Syntax.Counters
import Data.Vector (Vector)
import qualified Data.Vector as Vec

-- | Convert binary representation of inputs into human friendly Integers
--   TODO: make it something like a proper inverse of Inputs.deserialize
deserializeBinReps :: Counters -> Vector n -> Vector n
deserializeBinReps counters outputs =
  let (start, count) = getRange counters (Output, ReadAllBits)
      end = start + count
   in Vec.take start outputs <> Vec.drop end outputs

-- | Data structure for holding structured inputs
data Inputs n = Inputs
  { inputCounters :: Counters,
    inputPublic :: InputSequence n,
    inputPrivate :: InputSequence n
  }
  deriving (Eq, Show, Functor)

-- | Parse raw inputs into structured inputs and populate corresponding binary representations
deserialize :: (GaloisField n, Integral n) => Counters -> [n] -> [n] -> Either Error (Inputs n)
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

-- | Concatenate all inputs into a single list
flatten :: (GaloisField n, Integral n) => Inputs n -> ([n], [n])
flatten (Inputs _ public private) = (flattenInputSequence public, flattenInputSequence private)

-- | Size of all inputs
size :: (GaloisField n, Integral n) => Inputs n -> Int
size (Inputs counters _ _) = getCount counters PublicInput + getCount counters PrivateInput

toIntMap :: (GaloisField n, Integral n) => Inputs n -> IntMap n
toIntMap (Inputs counters public private) =
  let publicInputRanges = enumerate (getRanges counters [PublicInput])
      indexedPublicInput = IntMap.fromDistinctAscList $ zip publicInputRanges (flattenInputSequence public)
      privateInputRanges = enumerate (getRanges counters [PrivateInput])
      indexedPrivateInput = IntMap.fromDistinctAscList $ zip privateInputRanges (flattenInputSequence private)
   in indexedPublicInput <> indexedPrivateInput

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

new :: (GaloisField n, Integral n) => Seq (WriteType, n) -> InputSequence n
new =
  foldl
    ( \inputSequence (inputType, rawInputValue) ->
        case inputType of
          WriteField -> addField rawInputValue inputSequence
          WriteBool -> addBool rawInputValue inputSequence
          WriteUInt width -> addUInt width rawInputValue inputSequence
    )
    mempty

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
