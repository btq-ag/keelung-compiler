{-# LANGUAGE DeriveAnyClass #-}
{-# HLINT ignore "Use list comprehension" #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Data.Reference
  ( Ref (..),
    RefL (..),
    RefF (..),
    RefB (..),
    RefU (..),
    -- | limbs
    Limb (..),
    limbIsPositive,
    toRefLMultiplied,
    toRefLShifted,
    toRefL,
  )
where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import GHC.Generics (Generic)
import Keelung.Data.VarGroup (toSubscript)
import Keelung.Syntax

-- | For representing mixed variables in constraints
data Ref
  = -- | Field variable
    F RefF
  | -- | Boolean variable
    B RefB
  deriving (Eq, Ord, Generic, NFData)

instance Show Ref where
  show (F x) = show x
  show (B x) = show x

-- | For representing Boolean variables in constraints
data RefB
  = -- | Boolean output variable
    RefBO Var
  | -- | Boolean public input variable
    RefBI Var
  | -- | Boolean private input variable
    RefBP Var
  | -- | Boolean intermediate variable
    RefBX Var
  | -- | UInt bit variable
    RefUBit Width RefU Int
  deriving (Eq, Ord, Generic, NFData)

instance Show RefB where
  show (RefBO x) = "BO" ++ show x
  show (RefBI x) = "BI" ++ show x
  show (RefBP x) = "BP" ++ show x
  show (RefBX x) = "B" ++ show x
  show (RefUBit _ x i) = show x ++ "[" ++ show i ++ "]"

-- | For representing Field variables in constraints
data RefF
  = -- | Field output variable
    RefFO Var
  | -- | Field public input variable
    RefFI Var
  | -- | Field private input variable
    RefFP Var
  | -- | Field intermediate variable
    RefFX Var
  deriving (Eq, Ord, Generic, NFData)

instance Show RefF where
  show (RefFO x) = "FO" ++ show x
  show (RefFI x) = "FI" ++ show x
  show (RefFP x) = "FP" ++ show x
  show (RefFX x) = "F" ++ show x

-- | For representing Limbs in constraints
data RefL = RefL
  { refLLimb :: Limb,
    refLPowerOffset :: Int
  }
  deriving (Eq, Ord, Generic, NFData)

instance Show RefL where
  show (RefL (Limb ref limbWidth i sign') offset) = case (limbWidth, sign') of
    (0, _) -> "<Empty RefL>"
    (1, Left sign) -> (if sign then "" else "-") <> "2" <> toSuperscript offset <> "$" <> show (RefUBit 1 ref i)
    (1, Right signs) -> (if head signs then "" else "-") <> "2" <> toSuperscript offset <> "$" <> show (RefUBit 1 ref i)
    (2, Left sign) -> (if sign then "" else "-") <> "2" <> toSuperscript offset <> "$" <> show (RefUBit 1 ref i) <> " " <> (if sign then "+" else "-") <> " 2" <> toSuperscript (offset + 1) <> "$" <> show (RefUBit 1 ref (i + 1))
    (2, Right signs) -> (if head signs then "" else "-") <> "2" <> toSuperscript offset <> "$" <> show (RefUBit 1 ref i) <> " " <> (if last signs then "+" else "-") <> " 2" <> toSuperscript (offset + 1) <> "$" <> show (RefUBit 1 ref (i + 1))
    (_, Left sign) -> (if sign then "" else "-") <> "2" <> toSuperscript offset <> "$" <> show (RefUBit 1 ref i) <> (if sign then "+" else "-") <> " ... " <> (if sign then "+" else "-") <> " 2" <> toSuperscript (offset + limbWidth - 1) <> "$" <> show (RefUBit 1 ref (i + limbWidth - 1))
    (_, Right signs) -> (if head signs then "" else "-") <> "2" <> toSuperscript offset <> "$" <> show (RefUBit 1 ref i) <> " ... " <> (if last signs then "+" else "-") <> " 2" <> toSuperscript (offset + limbWidth - 1) <> "$" <> show (RefUBit 1 ref (i + limbWidth - 1))

-- | Helper function for converting integers to superscript strings
toSuperscript :: Int -> String
toSuperscript = map convert . show
  where
    convert '0' = '⁰'
    convert '1' = '¹'
    convert '2' = '²'
    convert '3' = '³'
    convert '4' = '⁴'
    convert '5' = '⁵'
    convert '6' = '⁶'
    convert '7' = '⁷'
    convert '8' = '⁸'
    convert _ = '⁹'

-- | For representing UInt variables in constraints
data RefU
  = -- | UInt output variable
    RefUO Width Var
  | -- | UInt public input variable
    RefUI Width Var
  | -- | UInt private input variable
    RefUP Width Var
  | -- | UInt intermediate variable
    RefUX Width Var
  deriving (Eq, Ord, Generic, NFData)

instance Show RefU where
  show ref = case ref of
    RefUO w x -> "UO" ++ toSubscript w ++ show x
    RefUI w x -> "UI" ++ toSubscript w ++ show x
    RefUP w x -> "UP" ++ toSubscript w ++ show x
    RefUX w x -> "U" ++ toSubscript w ++ show x

instance HasWidth RefU where
  widthOf (RefUO width _) = width
  widthOf (RefUI width _) = width
  widthOf (RefUP width _) = width
  widthOf (RefUX width _) = width

--------------------------------------------------------------------------------

data Limb = Limb
  { -- | Which RefU this limb belongs to
    lmbRef :: RefU,
    -- | How wide this limb is
    lmbWidth :: Width,
    -- | The offset of this limb
    lmbOffset :: Int,
    -- | Left: Sign of all bits
    -- | Right: Signs of each bit, LSB first
    lmbSigns :: Either Bool [Bool]
  }
  deriving (Show, Eq, Ord, Generic, NFData)

-- | A limb is considered "positive" if all of its bits are positive
limbIsPositive :: Limb -> Bool
limbIsPositive limb = case lmbSigns limb of
  Left sign -> sign
  Right signs -> and signs

-- | Construct a sequence of (Ref, n) pairs from a limb
toRefLMultiplied :: (GaloisField n, Integral n) => n -> Int -> Bool -> Limb -> (RefL, n)
toRefLMultiplied 0 _ _ _ = error "[ panic ] toRefL: multiplier must be non-zero"
toRefLMultiplied multiplyBy powerOffset positive limb =
  ( RefL limb powerOffset,
    if positive then multiplyBy else -multiplyBy
  )

-- | Specialized version of `toRefLMultiplied`, with `1` as the multiplier
toRefLShifted :: (GaloisField n, Integral n) => Int -> Bool -> Limb -> (RefL, n)
toRefLShifted = toRefLMultiplied 1

-- | Specialized version of `toRefLShifted`, with `1` as the multiplier, and `0` as the power offset
toRefL :: (GaloisField n, Integral n) => Bool -> Limb -> (RefL, n)
toRefL = toRefLMultiplied 1 0
