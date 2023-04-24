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
  | AssertLTEBoundTooSmallError Integer
  | AssertLTEBoundTooLargeError Integer Width
  | AssertLTBoundTooSmallError Integer
  | AssertLTBoundTooLargeError Integer Width
  | AssertGTEBoundTooSmallError Integer
  | AssertGTEBoundTooLargeError Integer Width
  | AssertGTBoundTooSmallError Integer
  | AssertGTBoundTooLargeError Integer Width
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (Error n)

instance (GaloisField n, Integral n) => Show (Error n) where
  show (ConflictingValuesB b1 b2) = "Cannot unify conflicting values: " <> show b1 <> " and " <> show b2
  show (ConflictingValuesF f1 f2) = "Cannot unify conflicting values: " <> show (N f1) <> " and " <> show (N f2)
  show (ConflictingValuesU u1 u2) = "Cannot unify conflicting values: " <> show (N u1) <> " and " <> show (N u2)
  show (AssertLTEBoundTooSmallError bound) = "assertLTE: the bound `" <> show bound <> "` is too restrictive, no UInt can be less than or equal to it"
  show (AssertLTEBoundTooLargeError bound width) =
    "assertLTE: the bound `"
      <> show bound
      <> "` is too large, since all UInt of bit width `"
      <> show width
      <> "` are less than or equal to `"
      <> show ((2 ^ width) - 1 :: Integer)
      <> "`"
  show (AssertLTBoundTooSmallError bound) = "assertLT: the bound `" <> show bound <> "` is too restrictive, no UInt can be less than it"
  show (AssertLTBoundTooLargeError bound width) =
    "assertLT: the bound `"
      <> show bound
      <> "` is too large, since all UInt of bit width `"
      <> show width
      <> "` are less than `"
      <> show ((2 ^ width) :: Integer)
      <> "`"
  show (AssertGTEBoundTooSmallError bound) = "assertGTE: the bound `" <> show bound <> "` is too small, all UInt are greater than or equal to it"
  show (AssertGTEBoundTooLargeError bound width) =
    "assertGTE: the bound `"
      <> show bound
      <> "` is too restrictive, since all UInt of bit width `"
      <> show width
      <> "` are less than `"
      <> show ((2 ^ width) :: Integer)
      <> "`"
  show (AssertGTBoundTooSmallError bound) = "assertGT: the bound `" <> show bound <> "` is too small, all UInt are greater than it"
  show (AssertGTBoundTooLargeError bound width) =
    "assertGT: the bound `"
      <> show bound
      <> "` is too restrictive, since all UInt of bit width `"
      <> show width
      <> "` are less than `"
      <> show ((2 ^ width) :: Integer)
      <> "`"

-- show AssertLTBoundTooSmallError =
--   "Using `0` as the bound for `assertLT` is too restrictive"