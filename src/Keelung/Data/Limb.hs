{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}

module Keelung.Data.Limb
  ( -- * Constructions
    Limb (..),
    newOperand,

    -- * Conversion
    toSlice,

    -- * Operations
    trim,

    -- * Query
    isPositive,

    -- * Signs of carry limbs
    Signs,
    splitAtSigns,
  )
where

import Control.DeepSeq (NFData)
import Data.Foldable (toList)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import GHC.Generics (Generic)
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice (..))
import Keelung.Syntax hiding (slice)
import Prelude hiding (null)

--------------------------------------------------------------------------------

type Signs = Seq (Bool, Width) -- (sign, width), LSB first

instance HasWidth Signs where
  widthOf = sum . fmap snd

splitAtSigns :: Int -> Signs -> (Signs, Signs)
splitAtSigns 0 xs = (Seq.Empty, xs)
splitAtSigns n xss = case Seq.viewl xss of
  Seq.EmptyL -> (Seq.Empty, Seq.Empty)
  (s, w) Seq.:< xs ->
    case n `compare` w of
      GT -> let (left, right) = splitAtSigns (n - w) xs in ((s, w) Seq.<| left, right)
      EQ -> ((s, w) Seq.<| Seq.Empty, xs)
      LT -> (Seq.singleton (s, n), (s, w - n) Seq.<| xs)

-- | TODO: remove this function
signsToListWithOffsets :: Signs -> [(Bool, Width, Int)]
signsToListWithOffsets = fst . foldl go ([], 0) . toList
  where
    go (acc, offset) (sign, width) = ((sign, width, offset) : acc, offset + width)

--------------------------------------------------------------------------------

data Limb
  = OperandLimb Slice Bool
  | CarryLimb RefU Signs
  deriving (Eq, Ord, Generic, NFData)

instance HasWidth Limb where
  widthOf (OperandLimb slice _) = widthOf slice
  widthOf (CarryLimb ref _) = widthOf ref

instance Show Limb where
  show limb =
    let (sign, terms) = showAsTerms limb
     in if sign then terms else "-" <> terms
    where
      -- \| For printing limbs as terms in a polynomial (signs are handled by the caller)
      --   returns (isPositive, string of the term)
      showAsTerms :: Limb -> (Bool, String)
      showAsTerms (CarryLimb ref signs) = (True, mconcat [(if sign then " + " else " - ") <> "2" <> toSuperscript offset <> show ref <> "[" <> show offset <> ":" <> show (offset + width) <> "]" | (sign, width, offset) <- signsToListWithOffsets signs])
      showAsTerms (OperandLimb slice sign) = (sign, show slice)

--------------------------------------------------------------------------------

-- | Construct "Slice"s from a "Limb" and a multiplier
toSlice :: (Integral n) => n -> Limb -> [(Slice, n)]
toSlice multiplier (OperandLimb slice sign) = [(slice, if sign then multiplier else -multiplier)]
toSlice multiplier (CarryLimb ref signs) = snd $ foldr (\(sign, width, offset) (i, acc) -> (i + width, (Slice ref i (i + width), if sign then multiplier * (2 ^ offset) else multiplier * (-(2 ^ offset))) : acc)) (0, []) (signsToListWithOffsets signs)

--------------------------------------------------------------------------------

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

-- | Construct a new operand Limb
newOperand :: Slice -> Bool -> Limb
newOperand = OperandLimb

--------------------------------------------------------------------------------

-- | Trim a 'Limb' to a given width.
trim :: Width -> Limb -> Limb
trim desiredWidth (OperandLimb (Slice ref start end) sign) = OperandLimb (Slice ref start (start + ((end - start) `min` desiredWidth))) sign
trim _ (CarryLimb ref signs) = CarryLimb ref signs

--------------------------------------------------------------------------------

-- | A limb is considered "positive" if all of its bits are positive
isPositive :: Limb -> Bool
isPositive (OperandLimb _ sign) = sign
isPositive (CarryLimb _ signs) = and [sign | (sign, _) <- toList signs]