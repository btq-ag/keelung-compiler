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
import Keelung.Compiler.Util
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
  | ParentOf
      Int -- length of this segment
      (Map RefU (Set Slice)) -- children
  | Free
      Int -- length of this segment
  deriving (Eq, Generic)

instance NFData Segment

instance Show Segment where
  show (Constant u) = "Constant" <> toSubscript (widthOf u) <> " " <> show u
  show (ChildOf limb) = "ChildOf" <> toSubscript (widthOf limb) <> " " <> show limb
  show (ParentOf len children) = case concatMap Set.toList (Map.elems children) of
    [] -> error "[ panic ] Segment.ParentOf with empty children"
    [slice] -> "ParentOf" <> toSubscript len <> " " <> show slice
    slices -> "ParentOf" <> toSubscript len <> " " <> show slices
  show (Free len) = "Free" <> toSubscript len

instance HasWidth Segment where
  widthOf (Constant u) = widthOf u
  widthOf (ChildOf limb) = widthOf limb
  widthOf (ParentOf len _) = len
  widthOf (Free len) = len

-- | Check if two Segments are of the same kind
sameKind :: Segment -> Segment -> Bool
sameKind (Constant _) (Constant _) = True
sameKind (Free _) (Free _) = True
sameKind (ChildOf _) (ChildOf _) = False
sameKind (ParentOf {}) (ParentOf {}) = False
sameKind _ _ = False

-- | Check if the width of a `Segment` is 0
null :: Segment -> Bool
null = (== 0) . widthOf

--------------------------------------------------------------------------------

-- | Split a `Segment` into two at a given index (relative to the starting offset of the Segement)
--   May result in invalid empty segments!
unsafeSplit :: Int -> Segment -> (Segment, Segment)
unsafeSplit index segment = case segment of
  Constant val -> (Constant (U.slice (0, index) val), Constant (U.slice (index, widthOf val) val))
  ChildOf slice -> let (slice1, slice2) = Slice.split index slice in (ChildOf slice1, ChildOf slice2)
  ParentOf len children ->
    let splittedChildren = fmap (Set.map (Slice.split index)) children
        children1 = fmap (Set.map fst) splittedChildren
        children2 = fmap (Set.map snd) splittedChildren
     in (ParentOf index children1, ParentOf (len - index) children2)
  Free len -> (Free index, Free (len - index))

--------------------------------------------------------------------------------

-- | See if 2 Segments can be glued together.
tryMerge :: Segment -> Segment -> Maybe Segment
tryMerge xs ys = case (xs, ys) of
  (Constant val1, Constant val2) -> Just (Constant (val2 <> val1))
  (ChildOf slice1, ChildOf slice2) -> case Slice.safeMerge slice1 slice2 of
    Left _ -> Nothing
    Right slice -> Just (ChildOf slice)
  (ParentOf _ _, ParentOf _ _) -> Nothing -- dunno how to merge parents together
  (Free len1, Free len2) ->
    if len1 + len2 == 0
      then Nothing
      else Just (Free (len1 + len2))
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
isValid (ParentOf len children) = len > 0 && not (Map.null children)
isValid (Free len) = len > 0
