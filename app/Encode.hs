{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BinaryLiterals #-}

module Encode (versionString, CircuitFormat(..), serializeR1CS, serializeInputAndWitness) where

-- import Data.Aeson.Encoding

import qualified Data.Bool as B
import Data.Aeson
import Data.Aeson.Encoding
import Data.Word
import Data.ByteString.Lazy (ByteString, pack)
import Data.ByteString.Lazy qualified as BS
import Data.ByteString.Builder
import Data.Binary qualified as B
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Data.IntMap qualified as IntMap
import Data.Vector (Vector)
import Data.List (intercalate)
import Keelung.Constraint.R1C (R1C (..))
import Keelung.Constraint.R1CS (R1CS (..), toR1Cs)
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Data.FieldInfo
import Keelung.Syntax
import Keelung.Syntax.Counters hiding (reindex)
import Keelung (FieldType(..))
import System.Random (genByteString)
import Data.Array (Ix(inRange))
import Data.Validation (Validate(_Either))

-- | IMPORTANT: Make sure major, minor and patch versions are updated
--   accordingly for every release.
compilerVersion :: (Int, Int)
compilerVersion = (0, 13)

patchVersion :: Int
patchVersion = 0

versionString :: String
versionString = intercalate "." [show (fst compilerVersion), show (snd compilerVersion), show patchVersion]

-- | J-R1CS – a JSON Lines format for R1CS
--   https://www.sikoba.com/docs/SKOR_GD_R1CS_Format.pdf

-- | Encodes inputs and witnesses in the JSON Lines text file format
--   the "inputs" field should contain both outputs & public inputs
--   the "witnesses" field should contain private inputs & rest of the witnesses
serializeInputAndWitness :: Integral n => Counters -> Vector n -> ByteString
serializeInputAndWitness counters witness =
  let outputAndPublicInputCount = getCount counters Output + getCount counters PublicInput
      (inputs, witnesses) = splitAt outputAndPublicInputCount $ toList witness
   in encodingToLazyByteString $
        pairs $
          pairStr "inputs" (list (integerText . toInteger) inputs)
            <> pairStr "witnesses" (list (integerText . toInteger) witnesses)

--------------------------------------------------------------------------------

-- | Encodes a R1CS in the JSON Lines text file format
serializeR1CS :: (GaloisField n, Integral n) => CircuitFormat -> R1CS n -> ByteString
serializeR1CS Aurora r1cs =
  BS.intercalate "\n" $
    map encodingToLazyByteString $
      header : toAurora r1cConstraints
  where
    -- the constraints are reindexed and all field numbers are converted to Integer
    r1cConstraints = map (fmap toInteger . reindexR1C r1cs) (toR1Cs r1cs)

    counters = r1csCounters r1cs

    characteristic = fromIntegral (fieldChar (r1csField r1cs))
    degree = fromIntegral (fieldDeg (r1csField r1cs))

    -- outputs & public inputs
    outputAndPublicInputCount = getCount counters Output + getCount counters PublicInput

    header :: Encoding
    header =
      pairs $
        pairStr "r1cs" $
          pairs $
            pairStr "version" (string versionString)
              <> pairStr "field_characteristic" (integerText characteristic)
              <> pairStr "extension_degree" (integerText degree)
              <> pairStr "instances" (int outputAndPublicInputCount)
              <> pairStr "witness" (int (getTotalCount counters - outputAndPublicInputCount)) -- private inputs & other intermediate variables after optimization
              <> pairStr "constraints" (int (length r1cConstraints))
              <> pairStr "optimized" (bool True)
-- | Binary representation used by Snarkjs:
-- | https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md
serializeR1CS Snarkjs r1cs = let info = r1csField r1cs in
  case fieldTypeData info of
    (Binary _) -> error "Snarkjs only allows prime fields."
    (Prime p) -> let header = toHeader p r1cs
                  in undefined
  where
    -- "r1cs, version 1, 3 sections"
    meta :: [Word8]
    meta = [0x72, 0x31, 0x63, 0x73, 0x01, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00]
    toHeader :: Integer -> R1CS n -> Either String [Word8]
    toHeader p r1cs = do let size = (fieldOrder . r1csField) r1cs
                         boundPrime <- B.bool (Left "Size of prime field is too large for Snarkjs (32 bits).")
                                              (Right $ word32LE $ fromIntegral size)
                                              (inRange (fromIntegral (minBound :: Word32), fromIntegral (maxBound :: Word32)) size)
                         let counters = r1csCounters r1cs
                             j = encode p
                             bin = BinHeader {
                               prime        = p
                             , nWires       = getTotalCount counters
                             , nPubOut      = getCount counters Output
                             , nPubIn       = getCount counters PublicInput
                             , nPrvIn       = getCount counters PrivateInput
                             , nLabels      = 0
                             , mConstraints = length $ r1csConstraints r1cs
                             }
                         return _

--------------------------------------------------------------------------------

-- | Encode a R1C for BTQ's Aurora implementation
-- | How to encode a Polynomial
--   The indices of variables are ordered as follows:
--    1. first index 0
--    2. then the negative indices (in decreasing order: -1, -2, ...)
--    3. finally the positive indices (in increasing order)
toAurora :: [R1C Integer] -> [Encoding]
toAurora r1cs = flip map r1cs $ \(R1C a b c) ->
  pairs $
    pairStr "A" (encodeEitherConstPoly a)
      <> pairStr "B" (encodeEitherConstPoly b)
      <> pairStr "C" (encodeEitherConstPoly c)
  where
    encodeEitherConstPoly :: Either Integer (Poly Integer) -> Encoding
    encodeEitherConstPoly (Left constant) = list encodeVarCoeff [(0, constant)]
    encodeEitherConstPoly (Right poly) = case Poly.constant poly of
      0 -> list encodeVarCoeff (negativeIndices ++ positiveIndices)
      n -> list encodeVarCoeff ((0, n) : negativeIndices ++ positiveIndices)
      where
        coeffs = Poly.coeffs poly
        negativeIndices = IntMap.toDescList $ IntMap.filterWithKey (\k _ -> k < 0) coeffs
        positiveIndices = IntMap.toAscList $ IntMap.filterWithKey (\k _ -> k > 0) coeffs


-- | How to encode a variable-coefficient pair
encodeVarCoeff :: (Var, Integer) -> Encoding
encodeVarCoeff (v, c) = list f [Left v, Right c]
  where
    f (Left var) = int var
    f (Right coeff) = integerText (toInteger coeff)
  
-- | Encode a R1C to Snarkjs' input format for Groth16
data CircuitFormat = Aurora | Snarkjs

data BinHeader = BinHeader {
    prime        :: Integer
,   nWires       :: Int
,   nPubOut      :: Int
,   nPubIn       :: Int
,   nPrvIn       :: Int
,   nLabels      :: Int
,   mConstraints :: Int
}

-- | Encode in little Endian format
encodeHeader :: BinHeader -> Builder
encodeHeader (BinHeader p wires pubout pubin prvIn labels mcons) =
  let primeBS = BS.reverse $ B.encode p
      byteLength = BS.length primeBS
   in word32LE (fromIntegral byteLength)
   <> lazyByteString primeBS
   <> word32LE (fromIntegral wires)
   <> word32LE (fromIntegral pubout)
   <> word32LE (fromIntegral pubin)
   <> word32LE (fromIntegral prvIn)
   <> word64LE (fromIntegral labels)
   <> word32LE (fromIntegral mcons)

toSnarkjsBin :: [R1C Integer] -> Builder
toSnarkjsBin = _

--------------------------------------------------------------------------------

-- | Variables of a R1CS are re-indexed so that:
--   index = 0:  reserved for the constant 1
--   index < 0:  reserved for output variables and public inputs variables
--   index > 0:  reserved for private input variables and all the other variables (witnesses)
reindexR1C :: R1CS n -> R1C n -> R1C n
reindexR1C r1cs (R1C a b c) =
  R1C
    (fmap (Poly.renumberVars reindex) a)
    (fmap (Poly.renumberVars reindex) b)
    (fmap (Poly.renumberVars reindex) c)
  where
    reindex :: Var -> Var
    reindex var
      | isPublicInputOrOutputVar var = -(var + 1) -- + 1 to avoid $0 the constant 1
      | otherwise = var + 1 -- + 1 to avoid $0 the constant 1
    isPublicInputOrOutputVar :: Var -> Bool
    isPublicInputOrOutputVar var =
      var < getCount (r1csCounters r1cs) Output + getCount (r1csCounters r1cs) PublicInput
