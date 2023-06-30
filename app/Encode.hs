{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Encode (serializeR1CS, serializeInputAndWitness) where

-- import Data.Aeson.Encoding

import Data.Aeson
import Data.Aeson.Encoding
import Data.ByteString.Lazy (ByteString)
import Data.ByteString.Lazy qualified as BS
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Data.IntMap qualified as IntMap
import Data.Vector (Vector)
import Keelung.Constraint.R1C (R1C (..))
import Keelung.Constraint.R1CS (R1CS (..), toR1Cs)
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Data.FieldInfo
import Keelung.Syntax
import Keelung.Syntax.Counters hiding (reindex)

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
serializeR1CS :: (GaloisField n, Integral n) => R1CS n -> ByteString
serializeR1CS r1cs =
  BS.intercalate "\n" $
    map encodingToLazyByteString $
      header : map toEncoding r1cConstraints
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
            pairStr "version" (string "0.11.0")
              <> pairStr "field_characteristic" (integerText characteristic)
              <> pairStr "extension_degree" (integerText degree)
              <> pairStr "instances" (int outputAndPublicInputCount)
              <> pairStr "witness" (int (getTotalCount counters - outputAndPublicInputCount)) -- private inputs & other intermediate variables after optimization
              <> pairStr "constraints" (int (length r1cConstraints))
              <> pairStr "optimized" (bool True)

--------------------------------------------------------------------------------

-- | How to encode a R1C
instance ToJSON (R1C Integer) where
  toEncoding (R1C a b c) =
    pairs $
      pairStr "A" (encodeEitherConstPoly a)
        <> pairStr "B" (encodeEitherConstPoly b)
        <> pairStr "C" (encodeEitherConstPoly c)
    where
      encodeEitherConstPoly :: Either Integer (Poly Integer) -> Encoding
      encodeEitherConstPoly (Left constant) = list encodeVarCoeff [(0, constant)]
      encodeEitherConstPoly (Right poly) = toEncoding poly

-- | How to encode a Polynomial
--   The indices of variables are ordered as follows:
--    1. first index 0
--    2. then the negative indices (in decreasing order: -1, -2, ...)
--    3. finally the positive indices (in increasing order)
instance ToJSON (Poly Integer) where
  toEncoding poly = case Poly.constant poly of
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