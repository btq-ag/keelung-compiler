{-# LANGUAGE DeriveGeneric #-}

-- | Value referenced by a Slice
module Keelung.Data.Segment
  ( -- * Construction
    Segment (..),

    -- * Properties
    null,
    sameKind,

    -- * Splitting and slicing
    unsafeSplit,
    tryMerge,

    -- * Testing
    isValid,
  )
where

import Control.DeepSeq (NFData)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Keelung (HasWidth, widthOf)
import Keelung.Data.Reference (RefU)
import Keelung.Data.Slice (Slice (..))
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Prelude hiding (map, null)

--------------------------------------------------------------------------------

-- | Either a constant value, or a part of an RefU, or a parent itself
data Segment
  = Constant U
  | ChildOf Slice -- part of some RefU
  | Parent
      Int -- length of this segment
      (Map RefU (Set Slice)) -- children
  | Unknown
      Int -- length of this segment
  deriving (Eq, Generic)

instance NFData Segment

instance Show Segment where
  show (Constant u) = "Constant[" <> show (widthOf u) <> "] " <> show u
  show (ChildOf limb) = "ChildOf[" <> show (widthOf limb) <> "] " <> show limb
  show (Parent len children) =
    "Parent["
      <> show len
      <> "] "
      <> show (fmap Set.toList (Map.elems children))
  show (Unknown len) = "Unknown[" <> show len <> "]"

instance HasWidth Segment where
  widthOf (Constant u) = widthOf u
  widthOf (ChildOf limb) = widthOf limb
  widthOf (Parent len _) = len
  widthOf (Unknown len) = len

-- | Check if two Segments are of the same kind
sameKind :: Segment -> Segment -> Bool
sameKind (Constant _) (Constant _) = True
sameKind (ChildOf _) (ChildOf _) = True
sameKind (Unknown _) (Unknown _) = True
sameKind (Parent {}) (Parent {}) = False
sameKind _ _ = False

-- | Check if the width of a `Segment` is 0
null :: Segment -> Bool
null = (== 0) . widthOf

--------------------------------------------------------------------------------

-- | Split a `Segment` into two at a given index (relative to the starting offset of the Segement)
--   May result in invalid empty segments!
unsafeSplit :: Int -> Segment -> (Segment, Segment)
unsafeSplit index segment = case segment of
  Constant val -> (Constant (U.slice val (0, index)), Constant (U.slice val (index, widthOf val)))
  ChildOf slice -> let (slice1, slice2) = Slice.split index slice in (ChildOf slice1, ChildOf slice2)
  Parent len children ->
    let splittedChildren = fmap (Set.map (Slice.split index)) children
        children1 = fmap (Set.map fst) splittedChildren
        children2 = fmap (Set.map snd) splittedChildren
     in (Parent index children1, Parent (len - index) children2)
  Unknown len -> (Unknown index, Unknown (len - index))

--------------------------------------------------------------------------------

-- | See if 2 Segments can be glued together.
tryMerge :: Segment -> Segment -> Maybe Segment
tryMerge xs ys = case (xs, ys) of
  (Constant val1, Constant val2) -> Just (Constant (val2 <> val1))
  (ChildOf slice1, ChildOf slice2) -> case Slice.safeMerge slice1 slice2 of
    Left _ -> Nothing
    Right slice -> Just (ChildOf slice)
  (Parent _ _, Parent _ _) -> Nothing -- dunno how to merge parents together
  (Unknown len1, Unknown len2) ->
    if len1 + len2 == 0
      then Nothing
      else Just (Unknown (len1 + len2))
  _ ->
    if null xs
      then Just ys
      else
        if null ys
          then Just xs
          else Nothing

--------------------------------------------------------------------------------

-- | Check if a `Segment` is valid
isValid :: Segment -> Bool
isValid (Constant val) = widthOf val > 0
isValid (ChildOf _) = True
isValid (Parent len children) = len > 0 && not (Map.null children)
isValid (Unknown len) = len > 0
