{-# LANGUAGE DeriveAnyClass #-}
{-# HLINT ignore "Use list comprehension" #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Data.Reference
  ( Ref (..),
    RefF (..),
    RefB (..),
    RefU (..),
    -- | limbs
    Limb (..),
    limbIsPositive,
    refUToLimbs,
  )
where

import Control.DeepSeq (NFData)
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
    -- | Which bit this limb starts at
    lmbOffset :: Int,
    -- | Left: Sign of all bits
    -- | Right: Signs of each bit, LSB first
    lmbSigns :: Either Bool [Bool]
  }
  deriving (Eq, Ord, Generic, NFData)

instance Show Limb where
  show (Limb ref limbWidth i sign') = case (limbWidth, sign') of
    (0, _) -> "<Empty Limb>"
    (1, Left sign) -> (if sign then "" else "-") <> "$" <> show (RefUBit 1 ref i)
    (1, Right signs) -> (if head signs then "" else "-") <> "$" <> show (RefUBit 1 ref i)
    (2, Left sign) -> (if sign then "" else "-") <> "{$" <> show (RefUBit 1 ref i) <> " " <> (if sign then "+" else "-") <> " 2" <> toSuperscript 1 <> "$" <> show (RefUBit 1 ref (i + 1)) <> "}"
    (2, Right signs) -> (if head signs then "" else "-") <> "{$" <> show (RefUBit 1 ref i) <> " " <> (if last signs then "+" else "-") <> " 2" <> toSuperscript 1 <> "$" <> show (RefUBit 1 ref (i + 1)) <> "}"
    (_, Left sign) -> (if sign then "" else "-") <> "$" <> show (RefUBit 1 ref i) <> " " <> (if sign then "+" else "-") <> " ... " <> (if sign then "+" else "-") <> " 2" <> toSuperscript (limbWidth - 1) <> "$" <> show (RefUBit 1 ref (i + limbWidth - 1))
    (_, Right signs) -> (if head signs then "" else "-") <> "$" <> show (RefUBit 1 ref i) <> " ... " <> (if last signs then "+" else "-") <> " 2" <> toSuperscript (limbWidth - 1) <> "$" <> show (RefUBit 1 ref (i + limbWidth - 1))

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

-- | A limb is considered "positive" if all of its bits are positive
limbIsPositive :: Limb -> Bool
limbIsPositive limb = case lmbSigns limb of
  Left sign -> sign
  Right signs -> and signs

-- | Convert a RefU to a bunch of Limbs
--   (in case that the field width is not large enough to hold the RefU)
refUToLimbs :: Width -> RefU -> [Limb]
refUToLimbs fieldWidth refU = step (widthOf refU) 0
  where
    step remainingWidth offset
      | remainingWidth <= fieldWidth = [Limb refU remainingWidth offset (Left True)]
      | otherwise = Limb refU fieldWidth offset (Left True) : step (remainingWidth - fieldWidth) (offset + fieldWidth)
