{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Data.Limb
  ( Limb (lmbRef, lmbWidth, lmbOffset, lmbSigns),
    Sign (..),
    signsToListWithOffsets,
    showAsTerms,
    new,
    isPositive,
    null,
    trim,
    split,
    MergeError (..),
    safeMerge,
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

data Sign
  = Single Bool
  | Multiple (Seq (Bool, Width)) -- (sign, width, offset), LSB first
  deriving (Eq, Ord, Show, Generic, NFData)

splitAtSigns :: Int -> Seq (Bool, Width) -> (Seq (Bool, Width), Seq (Bool, Width))
splitAtSigns 0 xs = (Seq.Empty, xs)
splitAtSigns n xss = case Seq.viewl xss of
  Seq.EmptyL -> (Seq.Empty, Seq.Empty)
  (s, w) Seq.:< xs ->
    if n > w
      then let (left, right) = splitAtSigns (n - w) xs in ((s, w) Seq.<| left, right)
      else (Seq.singleton (s, n), (s, w - n) Seq.<| xs)

takeSigns :: Int -> Seq (Bool, Width) -> Seq (Bool, Width)
takeSigns n xs = fst $ splitAtSigns n xs

-- | TODO: remove this function
signsToListWithOffsets :: Seq (Bool, Width) -> [(Bool, Width, Int)]
signsToListWithOffsets = fst . foldl go ([], 0) . toList
  where
    go (acc, offset) (sign, width) = ((sign, width, offset) : acc, offset + width)

--------------------------------------------------------------------------------

data Limb = Limb
  { -- | Which RefU this limb belongs to
    lmbRef :: RefU,
    -- | How wide this limb is
    lmbWidth :: Width,
    -- | Which bit this limb starts at
    lmbOffset :: Int,
    -- | Signs of the bits in this limb
    lmbSigns :: Sign
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
  (1, Single sign) -> (sign, "{$" <> show (RefUBit ref i) <> "}")
  (2, Single sign) -> (sign, "{$" <> show (RefUBit ref i) <> " + 2" <> toSuperscript 1 <> "$" <> show (RefUBit ref (i + 1)) <> "}")
  (_, Single sign) -> (sign, "{$" <> show (RefUBit ref i) <> " + ... + 2" <> toSuperscript (limbWidth - 1) <> "$" <> show (RefUBit ref (i + limbWidth - 1)) <> "}")
  -- (_, MultipleOld signs) ->
  --   let terms = mconcat [(if signs !! j then " + " else " - ") <> "2" <> toSuperscript j <> "$" <> show (RefUBit ref (i + j)) | j <- [0 .. limbWidth - 1]]
  --    in (True, "{" <> terms <> "}")
  (_, Multiple signs) ->
    (True, mconcat [(if sign then " + " else " - ") <> "2" <> toSuperscript offset <> "$" <> show (RefUBit ref (i + offset)) <> "[" <> show (i + offset) <> ":" <> show (i + offset + width) <> "]" | (sign, width, offset) <- signsToListWithOffsets signs])

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
  Single sign -> sign
  Multiple signs -> and [sign | (sign, _) <- toList signs]

-- | Trim a 'Limb' to a given width.
trim :: Width -> Limb -> Limb
trim width (Limb ref w offset (Single sign)) = Limb ref (w `min` width) offset (Single sign)
trim width (Limb ref w offset (Multiple signs)) = Limb ref (w `min` width) offset (Multiple (takeSigns (w `min` width) signs))

data SplitError = OffsetOutOfBound
  deriving (Eq)

instance Show SplitError where
  show OffsetOutOfBound = "Limb.SplitError: offset out of bound"

-- | Split a 'Limb' into two 'Limb's at a given index
safeSplit :: Int -> Limb -> Either SplitError (Limb, Limb)
safeSplit index (Limb ref w offset s)
  | index < 0 || index > w = Left OffsetOutOfBound
  | otherwise = case s of
      Single sign ->
        Right
          ( Limb ref index offset (Single sign),
            Limb ref (w - index) (offset + index) (Single sign)
          )
      Multiple signs ->
        let (leftSigns, rightSigns) = splitAtSigns index signs
         in Right
              ( Limb ref index offset (Multiple leftSigns),
                Limb ref (w - index) (offset + index) (Multiple rightSigns)
              )

-- | Split a 'Limb' into two 'Limb's at a given index of the RefU (unsafe exception-throwing version of `safeSplit`)
split :: Int -> Limb -> (Limb, Limb)
split index limb = case safeSplit index limb of
  Left err -> error $ "[ panic ] " <> show err
  Right limbs -> limbs

--------------------------------------------------------------------------------

-- | See if a Limb is empty
null :: Limb -> Bool
null (Limb _ w _ _) = w == 0

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
        (Single True, Single True) -> Single True
        (Single False, Single False) -> Single False
        (Single True, Single False) -> Multiple (Seq.fromList [(True, width1), (False, width2)])
        (Single False, Single True) -> Multiple (Seq.fromList [(False, width1), (True, width2)])
        (Single sign, Multiple signs) -> case Seq.viewl signs of
          Seq.EmptyL -> Single sign
          (s, w) Seq.:< signss ->
            if sign == s
              then Multiple ((s, w + width1) Seq.<| signss)
              else Multiple ((sign, width1) Seq.<| (s, w) Seq.<| signss)
        (Multiple signs, Single sign) -> case Seq.viewr signs of
          Seq.EmptyR -> Single sign
          signss Seq.:> (s, w) ->
            if sign == s
              then Multiple (signss Seq.|> (s, w + width2))
              else Multiple (signss Seq.|> (s, w) Seq.|> (sign, width2))
        (Multiple signsL, Multiple signsR) -> case (Seq.viewr signsL, Seq.viewl signsR) of
          (signsLs Seq.:> (s1, w1), (s2, w2) Seq.:< signsRs) ->
            if s1 == s2
              then Multiple ((signsLs Seq.|> (s1, w1 + w2)) Seq.>< signsRs)
              else Multiple (signsL Seq.>< signsR)
          (Seq.EmptyR, _) -> Multiple signsR
          (_, Seq.EmptyL) -> Multiple signsL