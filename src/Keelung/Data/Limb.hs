{-# LANGUAGE DeriveAnyClass #-}

module Keelung.Data.Limb
  ( Limb (lmbRef, lmbWidth, lmbOffset, lmbSigns),
    new,
    isPositive,
    refUToLimbs,
    trim,
  )
where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Keelung.Data.Reference
import Keelung.Syntax

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

-- | Construct a new 'Limb'
--   invariant: the width of the limb must be less than or equal to the width of the RefU
new :: RefU -> Width -> Int -> Either Bool [Bool] -> Limb
new refU width offset signs =
  if width > widthOf refU
    then error "[ panic ] Limb.new: Limb width exceeds RefU width"
    else
      Limb
        { lmbRef = refU,
          lmbWidth = width,
          lmbOffset = offset,
          lmbSigns = signs
        }

-- | A limb is considered "positive" if all of its bits are positive
isPositive :: Limb -> Bool
isPositive limb = case lmbSigns limb of
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

-- | Trim a 'Limb' to a given width.
trim :: Width -> Limb -> Limb
trim width (Limb ref w offset (Left sign)) = Limb ref (w `min` width) offset (Left sign)
trim width (Limb ref w offset (Right signs)) = Limb ref (w `min` width) offset (Right (take (w `min` width) signs))
