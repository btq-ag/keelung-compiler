{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Data.Limb
  ( Limb (..),
    limbRef,
    Signs,
    Sign (..),
    splitAtSigns,
    signsToListWithOffsets,
    showAsTerms,
    new,
    isPositive,
    null,
    trim,
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

data Sign
  = Single RefU Width Int Bool
  | Multiple RefU Signs
  deriving (Eq, Ord, Show, Generic, NFData)

instance HasWidth Sign where
  widthOf (Single _ w _ _) = w
  widthOf (Multiple ref _) = widthOf ref

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

newtype Limb = Limb {unLimb :: Sign} deriving (Eq, Ord, Generic, NFData)

limbRef :: Limb -> RefU
limbRef (Limb (Single ref _ _ _)) = ref
limbRef (Limb (Multiple ref _)) = ref

instance Show Limb where
  show limb =
    let (sign, terms) = showAsTerms limb
     in if sign then terms else "-" <> terms

instance HasWidth Limb where
  widthOf (Limb signs) = widthOf signs

-- | For printing limbs as terms in a polynomial (signs are handled by the caller)
--   returns (isPositive, string of the term)
showAsTerms :: Limb -> (Bool, String)
showAsTerms (Limb sign') = case sign' of
  Multiple ref signs -> (True, mconcat [(if sign then " + " else " - ") <> "2" <> toSuperscript offset <> show ref <> "[" <> show offset <> ":" <> show (offset + width) <> "]" | (sign, width, offset) <- signsToListWithOffsets signs])
  Single ref width offset sign -> case width of
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

-- | Construct a new 'Limb'
--   invariant: the width of the limb must be less than or equal to the width of the RefU
new :: RefU -> Width -> Int -> Sign -> Limb
new refU width offset signs =
  if width + offset > widthOf refU
    then error "[ panic ] Limb.new: Limb width exceeds RefU width"
    else Limb signs

-- | A limb is considered "positive" if all of its bits are positive
isPositive :: Limb -> Bool
isPositive limb = case unLimb limb of
  Single _ _ _ sign -> sign
  Multiple _ signs -> and [sign | (sign, _) <- toList signs]

-- | Trim a 'Limb' to a given width.
trim :: Width -> Limb -> Limb
trim desiredWidth (Limb (Single ref width offset sign)) = Limb (Single ref (width `min` desiredWidth) offset sign)
trim _ (Limb (Multiple ref signs)) = Limb (Multiple ref signs)

--------------------------------------------------------------------------------

-- | See if a Limb is empty
null :: Limb -> Bool
null limb = widthOf limb == 0
