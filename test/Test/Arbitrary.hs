{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use isNothing" #-}

-- | Instances of 'Arbitrary'
module Test.Arbitrary where

import Data.Field.Galois (GaloisField)
import Data.IntMap qualified as IntMap
import Data.Map qualified as Map
import Data.Set qualified as Set
import Keelung (Var)
import Keelung.Data.Limb (Limb)
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.RefUSegments (RefUSegments)
import Keelung.Data.RefUSegments qualified as RefUSegments
import Keelung.Data.Reference
import Keelung.Data.Segment (Segment)
import Keelung.Data.Segment qualified as Segment
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Keelung.Syntax (HasWidth (widthOf), Width)
import Test.QuickCheck

--------------------------------------------------------------------------------

-- | Default range of Var
defaultVar :: Gen Var
defaultVar = chooseInt (0, 5)

defaultWidth :: Gen Width
defaultWidth = chooseInt (1, 8)

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
        [ Segment.Constant <$> arbitraryUOfWidth width,
          Segment.ChildOf <$> arbitrarySliceOfWidth width,
          do
            childrenCount <- chooseInt (1, 4)
            children <- vectorOf childrenCount $ arbitrarySliceOfWidth width
            pure $ Segment.ParentOf width (Map.fromList (map (\child -> (Slice.sliceRefU child, Set.singleton child)) children))
        ]

instance Arbitrary Slice where
  arbitrary = defaultWidth >>= arbitrarySliceOfWidth

arbitrarySliceOfWidth :: Width -> Gen Slice
arbitrarySliceOfWidth width = do
  -- choose the starting offset of the slice first
  start <- chooseInt (0, 8)
  let end = start + width
  refUWidth <- chooseInt (end, end + 8)
  ref <- arbitraryRefUOfWidth refUWidth
  pure $ Slice.Slice ref start end

instance Arbitrary RefUSegments where
  arbitrary = do
    segments <- removeAdjectSameKind <$> arbitrary
    let intmap = snd $ foldr (\segment (index, acc) -> (index + widthOf segment, IntMap.insert index segment acc)) (0, mempty) segments
    let width = sum (map widthOf segments)
    ref <- arbitraryRefUOfWidth width
    pure $
      RefUSegments.normalize $
        RefUSegments.RefUSegments ref intmap
    where
      -- prevent segments of the same kind from being adjacent
      removeAdjectSameKind :: [Segment] -> [Segment]
      removeAdjectSameKind =
        foldr
          ( \segment acc -> case acc of
              [] -> [segment]
              (segment' : acc') -> if Segment.sameKind segment segment' then acc' else segment : acc
          )
          []

--------------------------------------------------------------------------------

instance Arbitrary Limb where
  arbitrary = do
    width <- chooseInt (1, 8)
    slice <- arbitrarySliceOfWidth width
    return $ Slice.toLimb slice

--------------------------------------------------------------------------------

-- | Generates valid PolyL
instance (Arbitrary n, Integral n, GaloisField n) => Arbitrary (PolyL n) where
  arbitrary =
    fst
      <$> ( do
              constant <- arbitrary
              refs <- arbitrary
              slices <- arbitrary
              case PolyL.new constant refs slices of
                Left _ -> return (error "impossible", False)
                Right poly -> return (poly, True)
          )
        `suchThat` (\(poly, successful) -> successful && PolyL.validate poly == Nothing)
