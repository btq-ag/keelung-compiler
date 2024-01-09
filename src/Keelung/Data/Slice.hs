module Keelung.Data.Slice
  ( -- * Construction
    Slice (..),
    fromLimb,
  )
where

import Keelung (HasWidth, widthOf)
import Keelung.Data.Limb (Limb)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference (RefU)
import Prelude hiding (map)

--------------------------------------------------------------------------------

-- | A "Slice" of a RefU
data Slice = Slice
  { sliceRefU :: RefU, -- the `RefU` this slice belongs to
    sliceStart :: Int, -- the starting offset of the slice
    sliceEnd :: Int -- the ending offset of the slice
  }
  deriving (Eq)

instance Show Slice where
  show (Slice ref start end) = show ref <> " [" <> show start <> " ... " <> show end <> ")"

instance HasWidth Slice where
  widthOf (Slice _ start end) = end - start

--------------------------------------------------------------------------------

-- | Construct a "Slice" from a "Limb"
fromLimb :: Limb -> Slice
fromLimb limb = Slice (Limb.lmbRef limb) (Limb.lmbOffset limb) (Limb.lmbOffset limb + widthOf limb)