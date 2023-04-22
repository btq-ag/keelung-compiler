{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.Compile.Error where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung (N (..))
import Keelung.Syntax (Width)

data Error n
  = ConflictingValuesB Bool Bool
  | ConflictingValuesF n n
  | ConflictingValuesU n n
  | AssertLTTooRestrictiveError
  | AssertGTTooRestrictiveError Width
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (Error n)

instance (GaloisField n, Integral n) => Show (Error n) where
  show (ConflictingValuesB b1 b2) = "Cannot unify conflicting values: " <> show b1 <> " and " <> show b2
  show (ConflictingValuesF f1 f2) = "Cannot unify conflicting values: " <> show (N f1) <> " and " <> show (N f2)
  show (ConflictingValuesU u1 u2) = "Cannot unify conflicting values: " <> show (N u1) <> " and " <> show (N u2)
  show (AssertGTTooRestrictiveError width) =
    "The bound for `assertGT` is too restrictive, since no UInt of bit width " <> show width <> " can be greater than " <> show ((2 ^ width) - 1 :: Integer)
  show AssertLTTooRestrictiveError =
    "Using `0` as the bound for `assertLT` is too restrictive"