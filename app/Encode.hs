{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Encode (serializeR1CS, serializeInputAndWitness) where

-- import Data.Aeson.Encoding

import Control.Arrow (left)
import Data.Aeson
import Data.Aeson.Encoding
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as BS
import Data.Field.Galois (GaloisField (char, deg))
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Proxy
import Keelung.Compiler.Util (Witness)
import Keelung.Constraint.Polynomial (Poly)
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Constraint.R1C (R1C (..))
import Keelung.Constraint.R1CS (CNEQ (..), R1CS (..), toR1Cs)
import Keelung.Syntax.VarCounters
import Keelung.Types

-- | J-R1CS – a JSON Lines format for R1CS
--   https://www.sikoba.com/docs/SKOR_GD_R1CS_Format.pdf

-- | Encodes a R1CS in the JSON Lines text file format
serializeR1CS :: (GaloisField n, Integral n) => R1CS n -> ByteString
serializeR1CS r1cs = serializeR1CS_ (fieldNumberProxy r1cs) (fmap toInteger (reindexR1CS r1cs))
  where
    fieldNumberProxy :: GaloisField n => R1CS n -> n
    fieldNumberProxy _ = asProxyTypeOf 0 Proxy

-- | Encodes inputs and witnesses in the JSON Lines text file format
--   the "inputs" field should contain both inputs and outputs
--   the "witnesses" field should contain rest of the witnesses
serializeInputAndWitness :: Integral n => [n] -> [n] -> Witness n -> ByteString
serializeInputAndWitness inputs outputs witnesses =
  let instances = inputs <> outputs
      instancesSize = length instances
      -- remove the inputs and outputs from the witnesses
      trimmedWitnesses = IntMap.elems $ IntMap.filterWithKey (\k _ -> k >= instancesSize) witnesses
   in encodingToLazyByteString $
        pairs $
          pairStr "inputs" (list (integerText . toInteger) instances)
            <> pairStr "witnesses" (list (integerText . toInteger) trimmedWitnesses)

--------------------------------------------------------------------------------

serializeR1CS_ :: GaloisField n => n -> R1CS Integer -> ByteString
serializeR1CS_ fieldNumber r1cs =
  BS.intercalate "\n" $
    map encodingToLazyByteString $
      header : map toEncoding r1cConstraints
  where
    r1cConstraints = toR1Cs r1cs

    varCounters = r1csVarCounters r1cs

    header :: Encoding
    header =
      pairs $
        pairStr "r1cs" $
          pairs $
            pairStr "version" (string "0.6.0")
              <> pairStr "field_characteristic" (integerText (toInteger (char fieldNumber)))
              <> pairStr "extension_degree" (integerText (toInteger (deg fieldNumber)))
              <> pairStr "instances" (int (pinnedVarSize varCounters)) -- inputs & outputs
              <> pairStr "witness" (int (totalVarSize varCounters - pinnedVarSize varCounters)) -- other ordinary variables
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
--   index < 0:  reserved for the input & output variables
--   index > 0:  reserved for the all the other variables (witnesses)
reindexR1CS :: R1CS n -> R1CS n
reindexR1CS r1cs =
  r1cs
    { r1csConstraints = map reindexR1C (r1csConstraints r1cs),
      r1csBoolVars = IntSet.map reindex (r1csBoolVars r1cs),
      r1csCNEQs = map (\(CNEQ x y m) -> CNEQ (left reindex x) (left reindex y) (reindex m)) (r1csCNEQs r1cs)
    }
  where
    reindexR1C :: R1C n -> R1C n
    reindexR1C (R1C a b c) =
      R1C
        (fmap (Poly.mapVars reindex) a)
        (fmap (Poly.mapVars reindex) b)
        (fmap (Poly.mapVars reindex) c)

    reindex :: Var -> Var
    reindex var
      | isInputOrOutputVar var = - var
      | otherwise = var

    isInputOrOutputVar :: Var -> Bool
    isInputOrOutputVar var = var < pinnedVarSize (r1csVarCounters r1cs)