{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.Compile.Error where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Serialize (Serialize)
import GHC.Generics (Generic)

data Error n
  = ConflictingValuesB Bool Bool
  | ConflictingValuesF n n
  | ConflictingValuesU n n
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (Error n)

instance (GaloisField n, Integral n) => Show (Error n) where
  show (ConflictingValuesB b1 b2) = "Cannot unify conflicting values: " <> show b1 <> " and " <> show b2
  show (ConflictingValuesF f1 f2) = "Conflicting values: " <> show f1 <> " and " <> show f2
  show (ConflictingValuesU u1 u2) = "Conflicting values: " <> show u1 <> " and " <> show u2