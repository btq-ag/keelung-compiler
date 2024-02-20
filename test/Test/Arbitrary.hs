-- | Instances of 'Arbitrary'
module Test.Arbitrary where

import Data.Bifunctor (first)
import Data.IntMap qualified as IntMap
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Keelung (Var)
import Keelung.Data.Limb (Limb)
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.SliceLookup (Segment, SliceLookup)
import Keelung.Data.SliceLookup qualified as SliceLookup
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Keelung.Syntax (HasWidth (widthOf), Width)
import Test.QuickCheck
import Data.Foldable (toList)

--------------------------------------------------------------------------------

-- | Default range of Var
defaultVar :: Gen Var
defaultVar = chooseInt (0, 10)

defaultWidth :: Gen Width
defaultWidth = chooseInt (0, 8)

instance Arbitrary RefU where
  arbitrary = defaultWidth >>= arbitraryRefUOfWidth

arbitraryRefUOfWidth :: Width -> Gen RefU
arbitraryRefUOfWidth width = do
  var <- defaultVar
  constructor <- elements [RefUO, RefUI, RefUP, RefUX]
  pure $ constructor width var

instance Arbitrary RefF where
  arbitrary =
    oneof
      [ RefFO <$> defaultVar,
        RefFI <$> defaultVar,
        RefFP <$> defaultVar,
        RefFX <$> defaultVar
      ]

instance Arbitrary RefB where
  arbitrary =
    oneof
      [ RefBO <$> defaultVar,
        RefBI <$> defaultVar,
        RefBP <$> defaultVar,
        RefBX <$> defaultVar
      ]

instance Arbitrary Ref where
  arbitrary = oneof [F <$> arbitrary, B <$> arbitrary]

--------------------------------------------------------------------------------

instance Arbitrary U where
  arbitrary = defaultWidth >>= arbitraryUOfWidth

arbitraryUOfWidth :: Width -> Gen U
arbitraryUOfWidth width = do
  value <- chooseInteger (0, 2 ^ width - 1)
  pure $ U.new width value

instance Arbitrary Segment where
  arbitrary = arbitrary >>= arbitrarySegmentOfSlice

arbitrarySegmentOfSlice :: Slice -> Gen Segment
arbitrarySegmentOfSlice (Slice.Slice _ start end) =
  let width = end - start
   in oneof
        [ SliceLookup.Constant <$> arbitraryUOfWidth width,
          SliceLookup.ChildOf <$> arbitrarySliceOfWidth width,
          do
            childrenCount <- defaultWidth
            children <- vectorOf childrenCount $ arbitrarySliceOfWidth width
            pure $ SliceLookup.Parent width (Map.fromList (map (\child -> (Slice.sliceRefU child, Set.singleton child)) children))
        ]

instance Arbitrary Slice where
  arbitrary = defaultWidth >>= arbitrarySliceOfWidth

arbitrarySliceOfWidth :: Width -> Gen Slice
arbitrarySliceOfWidth width = do
  -- choose the starting offset of the slice first
  start <- chooseInt (0, 16)
  let end = start + width
  refUWidth <- chooseInt (end, end + 16)
  ref <- arbitraryRefUOfWidth refUWidth
  pure $ Slice.Slice ref start end

instance Arbitrary SliceLookup where
  arbitrary = do
    start <- chooseInt (0, 16)
    segments <- removeAdjectSameKind <$> arbitrary
    let width = sum (map widthOf segments)
    var <- arbitraryRefUOfWidth width
    pure $
      SliceLookup.normalize $
        SliceLookup.SliceLookup
          (Slice.Slice var start (start + width))
          (snd $ foldr (\segment (index, acc) -> (index + widthOf segment, IntMap.insert index segment acc)) (start, mempty) segments)
    where
      -- prevent segments of the same kind from being adjacent
      removeAdjectSameKind :: [Segment] -> [Segment]
      removeAdjectSameKind =
        foldr
          ( \segment acc -> case acc of
              [] -> [segment]
              (segment' : acc') -> if SliceLookup.sameKindOfSegment segment segment' then acc' else segment : acc
          )
          []

--------------------------------------------------------------------------------

instance Arbitrary Limb where
  arbitrary = do
    width <- chooseInt (1, 8)
    slice <- arbitrarySliceOfWidth width
    return $ Slice.toLimb slice

--------------------------------------------------------------------------------

data Case = EmptyRefs | EmptyLimbs | BothNonEmpty

instance Arbitrary Case where
  arbitrary = elements [EmptyRefs, EmptyLimbs, BothNonEmpty]

instance (Arbitrary n, Integral n) => Arbitrary (PolyL n) where
  arbitrary = do
    result <- arbitrary
    (refs, slices) <- case result of
      EmptyRefs -> do
        slices <- arbitrary `suchThat` valid
        pure (mempty, Map.toList slices)
      EmptyLimbs -> do
        refs <- arbitrary `suchThat` valid
        pure (Map.toList refs, mempty)
      BothNonEmpty -> do
        refs <- arbitrary `suchThat` valid
        slices <- arbitrary `suchThat` valid
        pure (Map.toList refs, Map.toList slices)
    let limbs = fmap (first Slice.toLimb) slices
    constant <- arbitrary
    case PolyL.new constant refs limbs of
      Left _ -> error "impossible"
      Right poly -> pure poly
    where
      valid :: (Arbitrary n, Integral n) => Map a n -> Bool
      valid = not . Map.null . Map.filter (/= 0)