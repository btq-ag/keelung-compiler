{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Data.Limb
  ( Limb (lmbRef, lmbWidth, lmbOffset, lmbSigns),
    showAsTerms,
    new,
    isPositive,
    refUToLimbs,
    trim,
    split,
    MergeError (..),
    safeMerge,
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
  show limb =
    let (sign, terms) = showAsTerms limb
     in if sign then terms else "-" <> terms

instance HasWidth Limb where
  widthOf = lmbWidth

instance Semigroup Limb where
  (<>) = merge

-- | For printing limbs as terms in a polynomial (signs are handled by the caller)
--   returns (isPositive, string of the term)
showAsTerms :: Limb -> (Bool, String)
showAsTerms (Limb ref limbWidth i sign') = case (limbWidth, sign') of
  (0, _) -> (True, "{Empty Limb}")
  (1, Left sign) -> (sign, "{$" <> show (RefUBit ref i) <> "}")
  (2, Left sign) -> (sign, "{$" <> show (RefUBit ref i) <> " + 2" <> toSuperscript 1 <> "$" <> show (RefUBit ref (i + 1)) <> "}")
  (_, Left sign) -> (sign, "{$" <> show (RefUBit ref i) <> " + ... + 2" <> toSuperscript (limbWidth - 1) <> "$" <> show (RefUBit ref (i + limbWidth - 1)) <> "}")
  (_, Right signs) ->
    let terms = mconcat [(if signs !! j then " + " else " - ") <> "2" <> toSuperscript j <> "$" <> show (RefUBit ref (i + j)) | j <- [0 .. limbWidth - 1]]
     in (True, "{" <> terms <> "}")

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
  if width + offset > widthOf refU
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
refUToLimbs desiredWidth refU = step (widthOf refU) 0
  where
    width = widthOf refU `min` desiredWidth
    step remainingWidth offset
      | remainingWidth <= width = [Limb refU remainingWidth offset (Left True)]
      | otherwise = Limb refU width offset (Left True) : step (remainingWidth - width) (offset + width)

-- | Trim a 'Limb' to a given width.
trim :: Width -> Limb -> Limb
trim width (Limb ref w offset (Left sign)) = Limb ref (w `min` width) offset (Left sign)
trim width (Limb ref w offset (Right signs)) = Limb ref (w `min` width) offset (Right (take (w `min` width) signs))

data SplitError = OffsetOutOfBound
  deriving (Eq)

instance Show SplitError where
  show OffsetOutOfBound = "Limb.SplitError: offset out of bound"

-- | Split a 'Limb' into two 'Limb's at a given index of the RefU
safeSplit :: Int -> Limb -> Either SplitError (Limb, Limb)
safeSplit index (Limb ref w offset s)
  | index < 0 || index > w = Left OffsetOutOfBound
  | otherwise = case s of
      Left sign ->
        Right
          ( Limb ref ((index - offset) `max` 0) offset (Left sign),
            Limb ref ((w - index + offset) `min` w) index (Left sign)
          )
      Right signs ->
        Right
          ( Limb ref ((index - offset) `max` 0) offset (Right (take (index - offset) signs)),
            Limb ref ((w - index + offset) `min` w) index (Right (drop (index - offset) signs))
          )

-- | Split a 'Limb' into two 'Limb's at a given index of the RefU (unsafe exception-throwing version of `safeSplit`)
split :: Int -> Limb -> (Limb, Limb)
split index limb = case safeSplit index limb of
  Left err -> error $ "[ panic ] " <> show err
  Right limbs -> limbs

-- split :: Int -> Limb -> (Limb, Limb)
-- split index (Limb ref w offset (Left sign)) = (Limb ref index (offset + index) (Left sign), Limb ref (w - index) (offset + index) (Left sign))
-- split index (Limb ref w offset (Right signs)) = (Limb ref index (offset + index) (Right (take index signs)), Limb ref (w - index) (offset + index) (Right (drop index signs)))

--------------------------------------------------------------------------------

-- | Merge two Limbs into one, unsafe exception-throwing version of `safeMerge`
merge :: Limb -> Limb -> Limb
merge limb1 limb2 = case safeMerge limb1 limb2 of
  Left err -> error $ "[ panic ] " <> show err
  Right limb -> limb

data MergeError = NotSameRefU | NotAdjacent | Overlapping
  deriving (Eq)

instance Show MergeError where
  show NotSameRefU = "Limb.MergeError: two limbs are not of the same RefU"
  show NotAdjacent = "Limb.MergeError: two limbs are not adjacent with each other"
  show Overlapping = "Limb.MergeError: two limbs are overlapping with each other"

-- | Merge two Limbs into one, throwing MergeError if:
--    1. the two Limbs are not of the same `RefU`
--    2. the two Limbs are not adjacent
--    3. the two Limbs are overlapping
safeMerge :: Limb -> Limb -> Either MergeError Limb
safeMerge (Limb ref1 width1 offset1 signs1) (Limb ref2 width2 offset2 signs2)
  | ref1 /= ref2 = Left NotSameRefU
  | otherwise = case (offset1 + width1) `compare` offset2 of
      LT -> Left NotAdjacent
      GT -> Left Overlapping
      EQ -> Right $ Limb ref1 (width1 + width2) offset1 $ case (signs1, signs2) of
        (Left True, Left True) -> Left True
        (Left False, Left False) -> Left True
        (Left True, Left False) -> Right (replicate width1 True <> replicate width2 False)
        (Left False, Left True) -> Right (replicate width1 False <> replicate width2 True)
        (Left sign, Right signs) -> Right (replicate width1 sign <> signs)
        (Right signs, Left sign) -> Right (signs <> replicate width2 sign)
        (Right ss1, Right ss2) -> Right (ss1 <> ss2)