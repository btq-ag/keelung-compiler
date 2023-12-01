{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.Compile.Error where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung (N (..))
import Keelung.Syntax (Width)
import Keelung.Field (FieldType)

data Error n
  = ConflictingValuesB Bool Bool
  | ConflictingValuesF n n
  | ConflictingValuesU Integer Integer
  | AssertComparisonError Integer Ordering Integer
  | AssertLTEBoundTooSmallError Integer
  | AssertLTEBoundTooLargeError Integer Width
  | AssertLTBoundTooSmallError Integer
  | AssertLTBoundTooLargeError Integer Width
  | AssertGTEBoundTooSmallError Integer
  | AssertGTEBoundTooLargeError Integer Width
  | AssertGTBoundTooSmallError Integer
  | AssertGTBoundTooLargeError Integer Width
  | FieldTooSmall FieldType Width
  | FieldNotSupported FieldType
  deriving (Eq, Generic, NFData, Functor)

instance Serialize n => Serialize (Error n)

instance (GaloisField n, Integral n) => Show (Error n) where
  show (ConflictingValuesB b1 b2) = "Cannot unify conflicting Boolean values: " <> show b1 <> " and " <> show b2
  show (ConflictingValuesF f1 f2) = "Cannot unify conflicting Field elements: " <> show (N f1) <> " and " <> show (N f2)
  show (ConflictingValuesU u1 u2) = "Cannot unify conflicting UInt values: " <> show u1 <> " and " <> show u2
  show (AssertComparisonError x op y) = "Assertion on comparison doesn't hold: " <> show x <> " " <> op' <> " " <> show y
    where
      op' = case op of
        LT -> "<"
        EQ -> "="
        GT -> ">"
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
  show (FieldTooSmall fieldType width) = "The minimal bits required to represent the underling field " <> show fieldType <> " is " <> show width <> ", which is too small for formulating constraints"
  show (FieldNotSupported fieldType) = "The field " <> show fieldType <> " is not supported at the moment"