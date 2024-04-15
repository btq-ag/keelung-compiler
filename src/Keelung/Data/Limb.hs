{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Data.Limb
  ( Limb (..),
    limbRef,
    Signs,
    splitAtSigns,
    signsToListWithOffsets,
    newOperand,
    isPositive,
    trim,
    null,
  )
where

import Control.DeepSeq (NFData)
import Data.Foldable (toList)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import GHC.Generics (Generic)
import Keelung.Data.Reference
import Keelung.Syntax
import Prelude hiding (null)

--------------------------------------------------------------------------------

type Signs = Seq (Bool, Width) -- (sign, width), LSB first

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
  = OperandLimb
      RefU -- the reference of the limb
      Width -- width of the limb
      Int -- offset of which the limb starts
      Bool -- sign of the limb
  | CarryLimb RefU Signs
  deriving (Eq, Ord, Generic, NFData)

limbRef :: Limb -> RefU
limbRef (OperandLimb ref _ _ _) = ref
limbRef (CarryLimb ref _) = ref

instance HasWidth Limb where
  widthOf (OperandLimb _ w _ _) = w
  widthOf (CarryLimb ref _) = widthOf ref

instance Show Limb where
  show limb =
    let (sign, terms) = showAsTerms limb
     in if sign then terms else "-" <> terms

-- | For printing limbs as terms in a polynomial (signs are handled by the caller)
--   returns (isPositive, string of the term)
showAsTerms :: Limb -> (Bool, String)
showAsTerms (CarryLimb ref signs) = (True, mconcat [(if sign then " + " else " - ") <> "2" <> toSuperscript offset <> show ref <> "[" <> show offset <> ":" <> show (offset + width) <> "]" | (sign, width, offset) <- signsToListWithOffsets signs])
showAsTerms (OperandLimb ref width offset sign) = case width of
  0 -> (True, "{Empty Limb}")
  1 -> (sign, show ref <> "[" <> show offset <> "]")
  _ -> (sign, show ref <> "[" <> show offset <> ":" <> show (offset + width) <> "]")

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
--   invariant: the width of the limb must be less than or equal to the width of the RefU
newOperand :: RefU -> Width -> Int -> Bool -> Limb
newOperand refU width offset sign =
  if width + offset > widthOf refU
    then error "[ panic ] Limb.new: Limb width exceeds RefU width"
    else OperandLimb refU width offset sign

-- | A limb is considered "positive" if all of its bits are positive
isPositive :: Limb -> Bool
isPositive (OperandLimb _ _ _ sign) = sign
isPositive (CarryLimb _ signs) = and [sign | (sign, _) <- toList signs]

-- | Trim a 'Limb' to a given width.
trim :: Width -> Limb -> Limb
trim desiredWidth (OperandLimb ref width offset sign) = OperandLimb ref (width `min` desiredWidth) offset sign
trim _ (CarryLimb ref signs) = CarryLimb ref signs

--------------------------------------------------------------------------------

-- | See if a Limb is empty
null :: Limb -> Bool
null limb = widthOf limb == 0
